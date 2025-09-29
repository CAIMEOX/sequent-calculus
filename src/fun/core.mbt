///|
pub(all) enum Producer {
  Var(Var)
  Lit(Int)
  Mu(CoVar, Statement)
}

///|
pub(all) enum Consumer {
  CVar(CoVar)
}

///|
pub(all) enum Statement {
  Op(Op, Producer, Producer, Consumer)
  IfZero(Producer, Statement, Statement)
  Cut(Producer, Consumer)
}

///|
pub fn denoteP(self : Term) -> Producer {
  match self {
    TVar(v) => Var(v)
    TLiteral(i) => Lit(i)
    TOp(op, t1, t2) => {
      let alpha = CoVar(fresh())
      Mu(alpha, Op(op, t1.denoteP(), t2.denoteP(), CVar(alpha)))
    }
    TIfZero(t, t1, t2) => {
      let alpha : CoVar = CoVar(fresh())
      Mu(
        alpha,
        IfZero(
          t.denoteP(),
          Cut(t1.denoteP(), CVar(alpha)),
          Cut(t2.denoteP(), CVar(alpha)),
        ),
      )
    }
  }
}

///|
pub fn denotation(self : Term) -> Statement {
  Cut(self.denoteP(), CVar(Star))
}

///|
pub fn Consumer::is_value(self : Consumer) -> Bool {
  match self {
    CVar(_) => true
  }
}

///|
pub fn Statement::subst(
  self : Statement,
  covar : CoVar,
  term : Consumer,
) -> Statement {
  match self {
    Op(op, p1, p2, CVar(c)) if c == covar => Op(op, p1, p2, term)
    Op(op, p1, p2, c) => Op(op, p1, p2, c.subst(covar, term))
    IfZero(p, s1, s2) => IfZero(p, s1.subst(covar, term), s2.subst(covar, term))
    Cut(p, CVar(c)) if c == covar => Cut(p, term)
    Cut(p, c) => Cut(p, c.subst(covar, term))
  }
}

///|
pub fn Consumer::subst(
  self : Consumer,
  covar : CoVar,
  term : Consumer,
) -> Consumer {
  match self {
    CVar(c) if c == covar => term
    _ => self
  }
}

///|
pub fn Statement::step(self : Statement) -> Statement raise EvalError {
  match self {
    IfZero(Lit(0), s1, _) => s1
    IfZero(Lit(_), _, s2) => s2
    Op(op, Lit(v1), Lit(v2), c) => Cut(Lit(op.compute(v1, v2)), c)
    Cut(Mu(alpha, s), c) if c.is_value() => s.subst(alpha, c)
    _ => raise NonGroundTerm
  }
}

///|
impl Show for Producer with to_string(self) {
  match self {
    Lit(n) => n.to_string()
    Var(Var(i)) => "x" + i.to_string()
    Mu(c, s) => "μ \{c}.\{s}"
  }
}

///|
impl Show for Producer with output(self, l) {
  l.write_string(self.to_string())
}

///|
impl Show for Consumer with to_string(self) {
  match self {
    CVar(cv) => cv.to_string()
  }
}

///|
impl Show for Consumer with output(self, l) {
  l.write_string(self.to_string())
}

///|
impl Show for Statement with to_string(self) {
  match self {
    Op(op, p1, p2, c) => "\{op}(\{p1}, \{p2}; \{c})"
    IfZero(p, s1, s2) => "ifz(\{p}, \{s1}, \{s2})"
    Cut(p, c) => "⟨\{p} | \{c}⟩"
  }
}

///|
impl Show for Statement with output(self, l) {
  l.write_string(self.to_string())
}

///|
impl Show for Op with to_string(self) {
  match self {
    Add => "+"
    Sub => "-"
    Times => "*"
  }
}

///|
impl Show for Op with output(self, l) {
  l.write_string(self.to_string())
}

///|
pub fn Statement::eval(self : Statement) -> @buffer.Buffer {
  let buffer = @buffer.new()
  buffer.write_string("\{self}\n")
  loop (try? self.step()) {
    Ok(s) => {
      buffer.write_string("=> \{s}\n")
      continue try? s.step()
    }
    Err(_) => ()
  }
  buffer.write_char('□')
  buffer
}

///|
test {
  let term = TIfZero(TLiteral(2), TLiteral(5), TLiteral(10))
  let core = term.denotation()
  inspect(
    core,
    content="⟨μ α0.ifz(2, ⟨5 | α0⟩, ⟨10 | α0⟩) | ★⟩",
  )
  inspect(
    core.eval(),
    content=(
      #|⟨μ α0.ifz(2, ⟨5 | α0⟩, ⟨10 | α0⟩) | ★⟩
      #|=> ifz(2, ⟨5 | ★⟩, ⟨10 | ★⟩)
      #|=> ⟨10 | ★⟩
      #|□
    ),
  )
}
