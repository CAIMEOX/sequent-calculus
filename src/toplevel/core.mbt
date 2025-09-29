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
  Apply(Name, Array[Producer], Array[Consumer])
  Cut(Producer, Consumer)
}

///|
pub(all) enum CoreDef {
  Def(Name, Array[Var], Array[CoVar], Statement)
}

///|
impl Show for CoreDef with to_string(self) {
  match self {
    Def(n, vs, cvs, s) => {
      let vs_str = vs.map(x => x.to_string()).join(", ")
      let cvs_str = cvs.map(x => x.to_string()).join(", ")
      "def \{n}(\{vs_str};\{cvs_str}) := \{s}"
    }
  }
}

///|
impl Show for CoreDef with output(self, l) {
  l.write_string(self.to_string())
}

///|
pub(all) enum CoreProgram {
  Empty
  Cons(CoreDef, CoreProgram)
}

///|
impl Show for CoreProgram with to_string(self) {
  match self {
    Empty => ""
    Cons(d, p) => "\{d}\n\n\{p}"
  }
}

///|
impl Show for CoreProgram with output(self, l) {
  l.write_string(self.to_string())
}

///|
pub fn lookup(self : CoreProgram, n : Name) -> CoreDef? {
  match self {
    Empty => None
    Cons(Def(nm, vs, cvs, t), p) =>
      if nm == n {
        Some(Def(nm, vs, cvs, t))
      } else {
        p.lookup(n)
      }
  }
}

///|
pub fn denote_producer(self : Term) -> Producer {
  match self {
    TVar(v) => Var(v)
    TLiteral(i) => Lit(i)
    TOp(op, t1, t2) => {
      let alpha = CoVar(fresh())
      Mu(alpha, Op(op, t1.denote_producer(), t2.denote_producer(), CVar(alpha)))
    }
    TIfZero(t, t1, t2) => {
      let alpha : CoVar = CoVar(fresh())
      Mu(
        alpha,
        IfZero(
          t.denote_producer(),
          Cut(t1.denote_producer(), CVar(alpha)),
          Cut(t2.denote_producer(), CVar(alpha)),
        ),
      )
    }
    TLetIn(x, t1, t2) => {
      let alpha : CoVar = CoVar(fresh())
      Mu(
        alpha,
        Cut(
          t1.denote_producer(),
          CMuSim(x, Cut(t2.denote_producer(), CVar(alpha))),
        ),
      )
    }
    TApply(n, ps, cs) => {
      let alpha = CoVar(fresh())
      Mu(
        alpha,
        Apply(
          n,
          ps.map(t => t.denote_producer()),
          [..cs.map(Consumer::CVar(_)), CVar(alpha)],
        ),
      )
    }
  }
}

///|
pub fn denote_statement(self : Term) -> Statement {
  Cut(self.denote_producer(), CVar(Star))
}

///|
pub fn denote_def(self : TermDef) -> CoreDef {
  match self {
    Define(n, vs, cvs, t) => {
      let stmt = t.denote_producer()
      let alpha = CoVar(fresh())
      Def(n, vs, [..cvs, alpha], Cut(stmt, CVar(alpha)))
    }
  }
}

///|
pub fn denotation(self : TermProgram) -> CoreProgram {
  loop (self, (Empty : CoreProgram)) {
    (Empty, acc) => acc
    (Cons(f, p), acc) => continue (p, Cons(f.denote_def(), acc))
  }
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
    Op(op, p1, p2, c) =>
      Op(
        op,
        p1.subst_covar(covar, term),
        p2.subst_covar(covar, term),
        c.subst_covar(covar, term),
      )
    IfZero(p, s1, s2) =>
      IfZero(
        p.subst_covar(covar, term),
        s1.subst_covar(covar, term),
        s2.subst_covar(covar, term),
      )
    Cut(p, c) => Cut(p.subst_covar(covar, term), c.subst_covar(covar, term))
    Apply(n, ps, cs) =>
      Apply(
        n,
        ps.map(p => p.subst_covar(covar, term)),
        cs.map(c => c.subst_covar(covar, term)),
      )
  }
}

///|
pub fn Statement::subst_var(
  self : Statement,
  vr : Var,
  term : Producer,
) -> Statement {
  match self {
    Op(op, p1, p2, c) =>
      Op(
        op,
        p1.subst_var(vr, term),
        p2.subst_var(vr, term),
        c.subst_var(vr, term),
      )
    IfZero(p, s1, s2) =>
      IfZero(
        p.subst_var(vr, term),
        s1.subst_var(vr, term),
        s2.subst_var(vr, term),
      )
    Cut(p, c) => Cut(p.subst_var(vr, term), c.subst_var(vr, term))
    Apply(n, ps, cs) =>
      Apply(
        n,
        ps.map(p => p.subst_var(vr, term)),
        cs.map(c => c.subst_var(vr, term)),
      )
  }
}

///|
pub fn Consumer::subst_covar(
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
pub fn Consumer::subst_var(
  self : Consumer,
  vr : Var,
  term : Producer,
) -> Consumer {
  match self {
    CVar(c) => CVar(c)
    CMuSim(v, s) => CMuSim(v, s.subst_var(vr, term))
  }
}

///|
pub fn Producer::subst_var(
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
pub fn Producer::subst_covar(
  self : Producer,
  covar : CoVar,
  term : Consumer,
) -> Producer {
  match self {
    Mu(c, s) if c == covar => Mu(c, s)
    Mu(c, s) => Mu(c, s.subst_covar(covar, term))
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
    Apply(n, ps, cs) => {
      let ps_str = ps.map(x => x.to_string()).join(", ")
      let cs_str = cs.map(x => x.to_string()).join(", ")
      "\{n}(\{ps_str};\{cs_str})"
    }
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
pub fn Statement::step(
  self : Statement,
  ctx : CoreProgram,
) -> Statement raise EvalError {
  match self {
    IfZero(Lit(0), s1, _) => s1
    IfZero(Lit(_), _, s2) => s2
    Op(op, Lit(v1), Lit(v2), c) => Cut(Lit(op.compute(v1, v2)), c)
    Cut(p, CMuSim(v, s)) if p.is_value() => s.subst_var(v, p)
    Cut(Mu(alpha, s), c) if c.is_value() => s.subst_covar(alpha, c)
    Apply(n, ps, cs) if ps.iter().all(Producer::is_value) &&
      cs.iter().all(Consumer::is_value) =>
      match ctx.lookup(n) {
        Some(Def(_, vs, cvs, body)) => {
          guard vs.length() == ps.length() else {
            raise ArityMismatch(n, vs.length(), ps.length())
          }
          guard cs.length() == cvs.length() else {
            raise ArityMismatch(n, cs.length(), cvs.length())
          }
          println("\{vs} -> \{ps} | \{cvs} -> \{cs}")
          let substed_vs = vs
            .zip(ps)
            .fold(init=body, (stmt, vp) => stmt.subst_var(vp.0, vp.1))
          println("==> \{substed_vs}")
          cvs
          .zip(cs)
          .fold(init=substed_vs, (stmt, cp) => stmt.subst_covar(cp.0, cp.1))
        }
        None => raise DefNotFound(n)
      }
    _ => raise NonGroundTerm
  }
}

///|
pub fn Statement::eval(self : Statement, ctx : CoreProgram) -> @buffer.Buffer {
  let buffer = @buffer.new()
  buffer.write_string("\{self}\n")
  loop (try? self.step(ctx)) {
    Ok(s) => {
      buffer.write_string("=> \{s}\n")
      continue try? s.step(ctx)
    }
    Err(_) => ()
  }
  buffer.write_char('□')
  buffer
}

///|
test "ifz 2 then 5 else 10" {
  let term = TIfZero(TLiteral(2), TLiteral(5), TLiteral(10))
  let ctx : TermProgram = Empty
  let core = ctx.denotation()
  let core_expr = term.denote_statement()
  inspect(
    term.denote_producer(),
    content="μβ.ifz(2, ⟨5 | β⟩, ⟨10 | β⟩)",
  )
  inspect(
    core_expr.eval(core),
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
  let ctx : TermProgram = Empty
  let core = ctx.denotation()
  let core_expr = term.denote_statement()
  inspect(
    core_expr,
    content="⟨μα.⟨μβ.*(2, 2; β) | μ̃x.⟨μγ.*(x, x; γ) | α⟩⟩ | ★⟩",
  )
  inspect(
    core_expr.eval(core),
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

///|
test "fac" {
  let n : Var = Var(0)
  let _fac_def = Define(
    Name("fac"),
    [n],
    [],
    TIfZero(
      TVar(n),
      TLiteral(1),
      TOp(
        Times,
        TVar(n),
        TApply(Name("fac"), [TOp(Sub, TVar(n), TLiteral(1))], []),
      ),
    ),
  ).denote_def()
  let alpha = CoVar(fresh())
  let x : Var = Var(fresh())
  let r : Var = Var(fresh())
  let core_def = Def(
    Name("fac"),
    [n],
    [alpha],
    IfZero(
      Var(n),
      Cut(Lit(1), CVar(alpha)),
      Op(
        Sub,
        Var(n),
        Lit(1),
        CMuSim(
          x,
          Apply(Name("fac"), [Var(x)], [
            CMuSim(r, Op(Times, Var(n), Var(r), CVar(alpha))),
          ]),
        ),
      ),
    ),
  )
  let main = TApply(Name("fac"), [TLiteral(1)], [])
  let expr = main.denote_statement().eval(Cons(core_def, Empty))
  inspect(
    expr,
    content=(
      #|⟨μι.fac(1;ι) | ★⟩
      #|=> fac(1;★)
      #|=> ifz(1, ⟨1 | ★⟩, -(1, 1; μ̃d.fac(d;μ̃e.*(1, e; ★))))
      #|=> -(1, 1; μ̃d.fac(d;μ̃e.*(1, e; ★)))
      #|=> ⟨0 | μ̃d.fac(d;μ̃e.*(1, e; ★))⟩
      #|=> fac(0;μ̃e.*(1, e; ★))
      #|=> ifz(0, ⟨1 | μ̃e.*(1, e; ★)⟩, -(0, 1; μ̃d.fac(d;μ̃e.*(0, e; μ̃e.*(1, e; ★)))))
      #|=> ⟨1 | μ̃e.*(1, e; ★)⟩
      #|=> *(1, 1; ★)
      #|=> ⟨1 | ★⟩
      #|□
    ),
  )
}
