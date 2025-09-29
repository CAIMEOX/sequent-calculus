///|
/// Evaluate a statement and return the trace containing all individual steps.
pub fn[A] eval(start : Statement, prg : Program[A]) -> Array[Statement] {
  eval_helper(start, [start], prg)
}

///|
/// Helper function for evaluation with accumulator
fn[A] eval_helper(
  st : Statement,
  acc : Array[Statement],
  prg : Program[A],
) -> Array[Statement] {
  match eval_once(st, prg) {
    None => acc
    Some(st_next) => eval_helper(st_next, [..acc, st_next], prg)
  }
}

///|
/// Evaluate a statement in a program by one step.
pub fn[A] eval_once(st : Statement, prg : Program[A]) -> Statement? {
  match st {
    // ⟨μ x.st | c⟩ ▹ st[c/x]
    Cut(Mu(cv, inner_st), c) => Some(Subst::subst_covar(c, cv, inner_st))
    Cut(MuDyn(cv, inner_st), c) => Some(Subst::subst_covar(c, cv, inner_st))

    // ⟨p | μ~ x.st⟩ ▹ st[p/x]
    Cut(p, MuTilde(v, inner_st)) => Some(Subst::subst_var(p, v, inner_st))
    Cut(p, MuTildeDyn(v, inner_st)) => Some(Subst::subst_var(p, v, inner_st))

    // ⟨ctor(pargs;cargs) | case { ... ctor(vars;covars) ⇒ st }⟩ ▹ st[pargs/vars,cargs/covars]
    Cut(Constructor(ct, pargs, cargs), Case(patterns)) =>
      match find_pattern(patterns, ct) {
        Some(pattern) => {
          let var_pairs = pargs.mapi(fn(i, p) { (p, pattern.patvars[i]) })
          let covar_pairs = cargs.mapi(fn(i, c) { (c, pattern.patcovars[i]) })
          Some(Subst::subst_sim(var_pairs, covar_pairs, pattern.patstmt))
        }
        None => None
      }

    // ⟨cocase { ... dtor(vars;covars) ⇒ st } | dtor(pargs;cargs)⟩ ▹ st[pargs/vars,cargs/covars]
    Cut(Cocase(patterns), Destructor(dt, pargs, cargs)) =>
      match find_pattern_dtor(patterns, dt) {
        Some(pattern) => {
          let var_pairs = pargs.mapi(fn(i, p) { (p, pattern.patvars[i]) })
          let covar_pairs = cargs.mapi(fn(i, c) { (c, pattern.patcovars[i]) })
          Some(Subst::subst_sim(var_pairs, covar_pairs, pattern.patstmt))
        }
        None => None
      }

    // ⊙(n,m,c) ▹  ⟨n⊙m | c⟩
    Op(Lit(n), Mul, Lit(m), c) => Some(Cut(Lit(n * m), c))
    Op(Lit(n), Add, Lit(m), c) => Some(Cut(Lit(n + m), c))
    Op(Lit(n), Sub, Lit(m), c) => Some(Cut(Lit(n - m), c))
    Op(Lit(n), Div, Lit(m), c) =>
      if m != 0 {
        Some(Cut(Lit(n / m), c))
      } else {
        None
      }

    // ifz(0,s1,s2) ▹ s1
    // ifz(n,s1,s2) ▹ s2 (where n ≠ 0)
    IfZ(Lit(n), s1, s2) => if n == 0 { Some(s1) } else { Some(s2) }

    // f(ts;as) ▹ t[ts/xs;as/ys] if f(xs;ys) in P
    Fun(nm, pargs, cargs) =>
      match find_def(prg.defs, nm) {
        Some(def) => {
          let var_pairs = pargs.mapi(fn(i, p) { (p, def.pargs[i].0) })
          let covar_pairs = cargs.mapi(fn(i, c) { (c, def.cargs[i].0) })
          Some(Subst::subst_sim(var_pairs, covar_pairs, def.body))
        }
        None => None
      }

    // No reduction possible
    Done => None
    _ => None
  }
}

///|
/// Find a pattern matching the given constructor
fn find_pattern(patterns : Array[Pattern[Ctor]], ct : Ctor) -> Pattern[Ctor]? {
  for pattern in patterns {
    if pattern.xtor == ct {
      return Some(pattern)
    }
  }
  None
}

///|
/// Find a pattern matching the given destructor
fn find_pattern_dtor(
  patterns : Array[Pattern[Dtor]],
  dt : Dtor,
) -> Pattern[Dtor]? {
  for pattern in patterns {
    if pattern.xtor == dt {
      break Some(pattern)
    }
  } else {
    None
  }
}

///|
/// Find a definition by name
fn[A] find_def(defs : Array[Def[A]], name : String) -> Def[A]? {
  for def in defs {
    if def.name == name {
      return Some(def)
    }
  }
  None
}

///|
/// Evaluate the main statement of a program.
pub fn[A] eval_main(prg : Program[A]) -> Array[Statement]? {
  match find_def(prg.defs, "main") {
    Some(main_def) =>
      // ★ is the top-level continuation
      if main_def.cargs.length() > 0 {
        let top_covar = Covar("★")
        let first_covar = main_def.cargs[0].0
        let body_subst = Subst::subst_covar(
          top_covar,
          first_covar,
          main_def.body,
        )
        Some(eval(body_subst, prg))
      } else {
        Some(eval(main_def.body, prg))
      }
    None => None
  }
}

///|
/// Show implementation for Statement
impl Show for Statement with to_string(self) {
  match self {
    Cut(p, c) => "⟨" + Show::to_string(p) + " | " + Show::to_string(c) + "⟩"
    Op(p1, op, p2, c) =>
      Show::to_string(op) +
      "(" +
      Show::to_string(p1) +
      ", " +
      Show::to_string(p2) +
      "; " +
      Show::to_string(c) +
      ")"
    IfZ(p, s1, s2) =>
      "ifz(" +
      Show::to_string(p) +
      ", " +
      Show::to_string(s1) +
      ", " +
      Show::to_string(s2) +
      ")"
    Fun(nm, pargs, cargs) => {
      let ps = pargs.map(Show::to_string).join(", ")
      let cs = cargs.map(Show::to_string).join(", ")
      nm + "(" + ps + "; " + cs + ")"
    }
    Done => "Done"
  }
}

///|
impl Show for Statement with output(self, logger) {
  logger.write_string(self.to_string())
}

///|
impl Show for Dtor with output(self, logger) {
  logger.write_string(self.to_string())
}

///|
/// Show implementation for Producer
impl Show for Producer with to_string(self) {
  match self {
    Var(v) => v
    Lit(n) => n.to_string()
    Mu(cv, st) => "μ" + cv + "." + Show::to_string(st)
    MuDyn(cv, st) => "μᵈʸⁿ" + cv + "." + Show::to_string(st)
    Constructor(ct, pargs, cargs) => {
      let ps = pargs.map(Show::to_string).join(", ")
      let cs = cargs.map(Show::to_string).join(", ")
      Show::to_string(ct) + "(" + ps + "; " + cs + ")"
    }
    Cocase(patterns) => {
      let pts = patterns.map(Show::to_string).join(" | ")
      "cocase { " + pts + " }"
    }
  }
}

///|
impl Show for Producer with output(self, logger) {
  logger.write_string(self.to_string())
}

///|
/// Show implementation for Consumer
impl Show for Consumer with to_string(self) {
  match self {
    Covar(cv) => cv
    MuTilde(v, st) => "μ̃" + v + "." + Show::to_string(st)
    MuTildeDyn(v, st) => "μ̃ᵈʸⁿ" + v + "." + Show::to_string(st)
    Case(patterns) => {
      let pts = patterns.map(Show::to_string).join(" | ")
      "case { " + pts + " }"
    }
    Destructor(dt, pargs, cargs) => {
      let ps = pargs.map(Show::to_string).join(", ")
      let cs = cargs.map(Show::to_string).join(", ")
      Show::to_string(dt) + "(" + ps + "; " + cs + ")"
    }
  }
}

///|
impl Show for Consumer with output(self, logger) {
  logger.write_string(self.to_string())
}

///|
/// Show implementation for BinOp
impl Show for BinOp with to_string(self) {
  match self {
    Add => "+"
    Sub => "-"
    Mul => "*"
    Div => "/"
  }
}

///|
impl Show for BinOp with output(self, logger) {
  logger.write_string(self.to_string())
}

///|
/// Show implementation for Ctor
impl Show for Ctor with to_string(self) {
  match self {
    Nil => "Nil"
    Cons => "Cons"
    Tup => "Tup"
  }
}

///|
impl Show for Ctor with output(self, logger) {
  logger.write_string(self.to_string())
}

///|
/// Show implementation for Dtor
impl Show for Dtor with to_string(self) {
  match self {
    Fst => "Fst"
    Snd => "Snd"
    Head => "Head"
    Tail => "Tail"
    Ap => "Ap"
  }
}

///|
/// Show implementation for Pattern
impl[Tor : Show] Show for Pattern[Tor] with to_string(self) {
  let vars = self.patvars.join(", ")
  let cvars = self.patcovars.join(", ")
  Show::to_string(self.xtor) +
  "(" +
  vars +
  "; " +
  cvars +
  ") ⇒ " +
  Show::to_string(self.patstmt)
}

///|
impl[Tor : Show] Show for Pattern[Tor] with output(self, logger) {
  logger.write_string(self.to_string())
}

///|
/// Pretty print a trace of evaluation steps
pub fn print_trace(trace : Array[Statement]) -> String {
  trace
  .mapi(fn(i, st) {
    if i == 0 {
      "Initial: " + st.to_string()
    } else {
      "Step " + i.to_string() + ": " + st.to_string()
    }
  })
  .join("\n")
}
