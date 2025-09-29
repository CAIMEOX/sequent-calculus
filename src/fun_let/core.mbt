///|
pub(all) enum Producer {
  Var(Var)
  Lit(Int)
  Mu(CoVar, Statement)
}

///|
pub(all) enum Consumer {
  CVar(CoVar)
  CMuSim(Var, Statement)
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
    TLetIn(x, t1, t2) => {
      let alpha : CoVar = CoVar(fresh())
      Mu(alpha, Cut(t1.denoteP(), CMuSim(x, Cut(t2.denoteP(), CVar(alpha)))))
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
    CMuSim(_, _) => true
  }
}

///|
pub fn Producer::is_value(self : Producer) -> Bool {
  match self {
    Lit(_) => true
    Var(_) => false
    Mu(_, _) => false
  }
}

///|
pub fn Statement::subst_covar(
  self : Statement,
  covar : CoVar,
  term : Consumer,
) -> Statement {
  match self {
    Op(op, p1, p2, CVar(c)) if c == covar => Op(op, p1, p2, term)
    Op(op, p1, p2, c) => Op(op, p1, p2, c.subst(covar, term))
    IfZero(p, s1, s2) =>
      IfZero(p, s1.subst_covar(covar, term), s2.subst_covar(covar, term))
    Cut(p, CVar(c)) if c == covar => Cut(p, term)
    Cut(p, c) => Cut(p, c.subst(covar, term))
  }
}

///|
pub fn Statement::subst_var(
  self : Statement,
  vr : Var,
  term : Producer,
) -> Statement {
  match self {
    Op(op, p1, p2, c) => Op(op, p1.subst(vr, term), p2.subst(vr, term), c)
    IfZero(p, s1, s2) =>
      IfZero(p.subst(vr, term), s1.subst_var(vr, term), s2.subst_var(vr, term))
    Cut(p, c) => Cut(p.subst(vr, term), c)
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
    CVar(c) => CVar(c)
    CMuSim(v, s) => CMuSim(v, s.subst_covar(covar, term))
  }
}

///|
pub fn Producer::subst(
  self : Producer,
  covar : Var,
  term : Producer,
) -> Producer {
  match self {
    Mu(c, s) => Mu(c, s.subst_var(covar, term))
    Var(v) if v == covar => term
    Var(v) => Var(v)
    Lit(n) => Lit(n)
  }
}

///|
impl Show for Producer with to_string(self) {
  match self {
    Lit(n) => n.to_string()
    Var(v) => v.to_string()
    Mu(c, s) => "μ\{c}.\{s}"
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
    CMuSim(v, s) => "μ̃\{v}.\{s}"
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
pub fn Statement::step(self : Statement) -> Statement raise EvalError {
  match self {
    IfZero(Lit(0), s1, _) => s1
    IfZero(Lit(_), _, s2) => s2
    Op(op, Lit(v1), Lit(v2), c) => Cut(Lit(op.compute(v1, v2)), c)
    Cut(p, CMuSim(v, s)) if p.is_value() => s.subst_var(v, p)
    Cut(Mu(alpha, s), c) if c.is_value() => s.subst_covar(alpha, c)
    _ => raise NonGroundTerm
  }
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
test "ifz 2 then 5 else 10" {
  let term = TIfZero(TLiteral(2), TLiteral(5), TLiteral(10))
  let core = term.denotation()
  inspect(core, content="⟨μα.ifz(2, ⟨5 | α⟩, ⟨10 | α⟩) | ★⟩")
  inspect(
    core.eval(),
    content=(
      #|⟨μα.ifz(2, ⟨5 | α⟩, ⟨10 | α⟩) | ★⟩
      #|=> ifz(2, ⟨5 | ★⟩, ⟨10 | ★⟩)
      #|=> ⟨10 | ★⟩
      #|□
    ),
  )
}

///|
test "let x = 2 * 2 in x * x" {
  let x : Var = Var(0)
  let term = TLetIn(
    x,
    TOp(Times, TLiteral(2), TLiteral(2)),
    TOp(Times, TVar(x), TVar(x)),
  )
  let core = term.denotation()
  inspect(
    core,
    content="⟨μα.⟨μβ.*(2, 2; β) | μ̃x.⟨μγ.*(x, x; γ) | α⟩⟩ | ★⟩",
  )
  inspect(
    core.eval(),
    content=(
      #|⟨μα.⟨μβ.*(2, 2; β) | μ̃x.⟨μγ.*(x, x; γ) | α⟩⟩ | ★⟩
      #|=> ⟨μβ.*(2, 2; β) | μ̃x.⟨μγ.*(x, x; γ) | ★⟩⟩
      #|=> *(2, 2; μ̃x.⟨μγ.*(x, x; γ) | ★⟩)
      #|=> ⟨4 | μ̃x.⟨μγ.*(x, x; γ) | ★⟩⟩
      #|=> ⟨μγ.*(4, 4; γ) | ★⟩
      #|=> *(4, 4; ★)
      #|=> ⟨16 | ★⟩
      #|□

    ),
  )
}
