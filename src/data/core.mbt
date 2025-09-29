///|
pub(all) enum Producer {
  Var(Var)
  Lit(Int)
  Mu(CoVar, Statement)
  Ktor(Tor, Array[Producer], Array[Consumer])
  Cocase(Array[Clause])
}

///|
pub(all) struct Clause(Tor, Array[Var], Array[CoVar], Statement)

///|
pub(all) enum Consumer {
  CVar(CoVar)
  CMuSim(Var, Statement)
  CDtor(Tor, Array[Producer], Array[Consumer])
  CCase(Array[Clause])
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
    TCtor(tor, ts) => Ktor(tor, ts.map(t => t.denote_producer()), [])
    TCase(t, cases) => {
      let alpha = CoVar(fresh())
      Mu(
        alpha,
        Cut(t.denote_producer(), CCase(cases.map(_.denote_clause(Some(alpha))))),
      )
    }
    TDtor(t, tor, ts) => {
      let alpha = CoVar(fresh())
      Mu(
        alpha,
        Cut(
          t.denote_producer(),
          CDtor(tor, ts.map(t => t.denote_producer()), [CVar(alpha)]),
        ),
      )
    }
    TCocase(cs) => Cocase(cs.map(_.denote_clause(None)))
  }
}

///|
pub fn denote_clause(self : Case, ret : CoVar?) -> Clause {
  let Case(tor, vs, t) = self
  match ret {
    Some(alpha) => Clause(tor, vs, [], Cut(t.denote_producer(), CVar(alpha)))
    None => {
      let beta = CoVar(fresh())
      Clause(tor, vs, [beta], Cut(t.denote_producer(), CVar(beta)))
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
    CCase(_) => true
    CDtor(_, _, _) => true
  }
}

///|
pub fn Producer::is_value(self : Producer) -> Bool {
  match self {
    Lit(_) => true
    Var(_) => false
    Mu(_, _) => false
    Ktor(_, ps, _) => ps.iter().all(Producer::is_value)
    Cocase(_) => true
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
    CDtor(tor, ps, cs) =>
      CDtor(
        tor,
        ps.map(p => p.subst_covar(covar, term)),
        cs.map(c => c.subst_covar(covar, term)),
      )
    CCase(cls) => CCase(cls.map(cl => cl.subst_covar(covar, term)))
  }
}

///|
pub fn Clause::subst_covar(
  self : Clause,
  covar : CoVar,
  term : Consumer,
) -> Clause {
  let Clause(tor, vs, cvs, s) = self
  Clause(tor, vs, cvs, s.subst_covar(covar, term))
}

///|
pub fn Clause::subst_var(self : Clause, vr : Var, term : Producer) -> Clause {
  let Clause(tor, vs, cvs, s) = self
  Clause(tor, vs, cvs, s.subst_var(vr, term))
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
    CDtor(tor, ps, cs) =>
      CDtor(
        tor,
        ps.map(p => p.subst_var(vr, term)),
        cs.map(c => c.subst_var(vr, term)),
      )
    CCase(cls) => CCase(cls.map(cl => cl.subst_var(vr, term)))
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
    Ktor(tor, ps, cs) =>
      Ktor(
        tor,
        ps.map(p => p.subst_var(covar, term)),
        cs.map(c => c.subst_var(covar, term)),
      )
    Cocase(cls) => Cocase(cls.map(cl => cl.subst_var(covar, term)))
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
    Ktor(tor, ps, cs) =>
      Ktor(
        tor,
        ps.map(p => p.subst_covar(covar, term)),
        cs.map(c => c.subst_covar(covar, term)),
      )
    Cocase(cls) => Cocase(cls.map(cl => cl.subst_covar(covar, term)))
  }
}

///|
impl Show for Producer with to_string(self) {
  match self {
    Lit(n) => n.to_string()
    Var(v) => v.to_string()
    Mu(c, s) => "μ\{c}.\{s}"
    Ktor(tor, ps, cs) => {
      let ps_str = ps.map(x => x.to_string()).join(", ")
      let cs_str = cs.map(x => x.to_string()).join(", ")
      "\{tor}(\{ps_str}; \{cs_str})"
    }
    Cocase(cls) => {
      let cls_str = cls.map(cl => cl.to_string()).join(" | ")
      "cocase { \{cls_str} }"
    }
  }
}

///|
impl Show for Clause with to_string(self) {
  let Clause(tor, vs, cvs, s) = self
  let vs_str = vs.map(x => x.to_string()).join(", ")
  let cvs_str = cvs.map(x => x.to_string()).join(", ")
  "\{tor}(\{vs_str}; \{cvs_str}) => \{s}"
}

///|
impl Show for Clause with output(self, l) {
  l.write_string(self.to_string())
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
    CDtor(tor, ps, cs) => {
      let ps_str = ps.map(x => x.to_string()).join(", ")
      let cs_str = cs.map(x => x.to_string()).join(", ")
      "\{tor}(\{ps_str}; \{cs_str})"
    }
    CCase(cls) => {
      let cls_str = cls.map(cl => cl.to_string()).join(" | ")
      "case { \{cls_str} }"
    }
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
            raise ArityMismatch(n.inner(), vs.length(), ps.length())
          }
          guard cs.length() == cvs.length() else {
            raise ArityMismatch(n.inner(), cs.length(), cvs.length())
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
    Cut(Ktor(tor, ps, cs), CCase(cls)) if ps.iter().all(Producer::is_value) &&
      cs.iter().all(Consumer::is_value) =>
      match Clause::match_tor(cls, tor) {
        Some(Clause(_, vs, cvs, s)) => {
          guard vs.length() == ps.length() else {
            raise ArityMismatch(tor.inner(), vs.length(), ps.length())
          }
          guard cvs.length() == cs.length() else {
            raise ArityMismatch(tor.inner(), cvs.length(), cs.length())
          }
          let substed_vs = vs
            .zip(ps)
            .fold(init=s, (stmt, vp) => stmt.subst_var(vp.0, vp.1))
          cvs
          .zip(cs)
          .fold(init=substed_vs, (stmt, cp) => stmt.subst_covar(cp.0, cp.1))
        }
        None => raise CtorNotFound(tor)
      }
    Cut(Cocase(cls), CDtor(tor, ps, cs)) if ps.iter().all(Producer::is_value) &&
      cs.iter().all(Consumer::is_value) =>
      match Clause::match_tor(cls, tor) {
        Some(Clause(_, vs, cvs, s)) => {
          guard vs.length() == ps.length() else {
            raise ArityMismatch(tor.inner(), vs.length(), ps.length())
          }
          guard cvs.length() == cs.length() else {
            raise ArityMismatch(tor.inner(), cvs.length(), cs.length())
          }
          let substed_vs = vs
            .zip(ps)
            .fold(init=s, (stmt, vp) => stmt.subst_var(vp.0, vp.1))
          cvs
          .zip(cs)
          .fold(init=substed_vs, (stmt, cp) => stmt.subst_covar(cp.0, cp.1))
        }
        None => raise DtorNotFound(tor)
      }
    _ => raise NonGroundTerm
  }
}

///|
pub fn Clause::match_tor(self : Array[Clause], tor : Tor) -> Clause? {
  for cl in self {
    if cl.0 == tor {
      break Some(cl)
    }
  } else {
    None
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

///|
test "tup and swap" {
  let x : Var = Var(0)
  let alpha = CoVar(0)
  let tup = Tor("Tup")
  let swap_def = Def(
    Name("swap"),
    [x],
    [alpha],
    Cut(
      Var(x),
      CCase([
        Clause(
          tup,
          [Var(1), Var(2)],
          [],
          Cut(Ktor(tup, [Var(2), Var(1)], []), CVar(alpha)),
        ),
      ]),
    ),
  )
  let pair = TApply(Name("swap"), [TCtor(tup, [TLiteral(2), TLiteral(3)])], [])
  let expr = pair.denote_statement().eval(Cons(swap_def, Empty))
  inspect(
    expr,
    content=(
      #|⟨μα.swap(Tup(2, 3; );α) | ★⟩
      #|=> swap(Tup(2, 3; );★)
      #|=> ⟨Tup(2, 3; ) | case { Tup(y, z; ) => ⟨Tup(z, y; ) | ★⟩ }⟩
      #|=> ⟨Tup(3, 2; ) | ★⟩
      #|□
    ),
  )
}

///|
test "codata tup" {
  let x : Var = Var(0)
  let alpha = CoVar(0)
  let beta = CoVar(1)
  let fst = Tor("fst")
  let snd = Tor("snd")
  let swap_lazy_def = Def(
    Name("swap_lazy"),
    [x],
    [alpha],
    Cut(
      Cocase([
        Clause(fst, [], [beta], Cut(Var(x), CDtor(snd, [], [CVar(beta)]))),
        Clause(snd, [], [beta], Cut(Var(x), CDtor(fst, [], [CVar(beta)]))),
      ]),
      CVar(alpha),
    ),
  )
  inspect(
    swap_lazy_def,
    content="def swap_lazy(x;α) := ⟨cocase { fst(; β) => ⟨x | snd(; β)⟩ | snd(; β) => ⟨x | fst(; β)⟩ } | α⟩",
  )
  let alpha2 = CoVar(4)
  let p = Cocase([
    Clause(fst, [], [alpha2], Cut(Lit(1), CVar(alpha2))),
    Clause(snd, [], [alpha2], Op(Times, Lit(2), Lit(3), CVar(alpha2))),
  ])
  let term = Apply(Name("swap_lazy"), [p], [CDtor(snd, [], [CVar(Star)])])
  inspect(
    p,
    content="cocase { fst(; ε) => ⟨1 | ε⟩ | snd(; ε) => *(2, 3; ε) }",
  )
  let expr = term.eval(Cons(swap_lazy_def, Empty))
  inspect(
    expr,
    content=(
      #|swap_lazy(cocase { fst(; ε) => ⟨1 | ε⟩ | snd(; ε) => *(2, 3; ε) };snd(; ★))
      #|=> ⟨cocase { fst(; β) => ⟨cocase { fst(; ε) => ⟨1 | ε⟩ | snd(; ε) => *(2, 3; ε) } | snd(; β)⟩ | snd(; β) => ⟨cocase { fst(; ε) => ⟨1 | ε⟩ | snd(; ε) => *(2, 3; ε) } | fst(; β)⟩ } | snd(; ★)⟩
      #|=> ⟨cocase { fst(; ε) => ⟨1 | ε⟩ | snd(; ε) => *(2, 3; ε) } | fst(; ★)⟩
      #|=> ⟨1 | ★⟩
      #|□

    ),
  )
}
