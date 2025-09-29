///|
pub fn Producer::is_value(self : Producer) -> Bool {
  match self {
    Lit(_) | Var(_) | Cocase(_) => true
    Constructor(_, prds, _) => prds.iter().all(Producer::is_value)
    Mu(_) | MuDyn(_) => false
  }
}

///|
pub(open) trait Focus {
  focus(Self) -> Self
}

///|
impl[A] Focus for Pattern[A] with focus(self) {
  { ..self, patstmt: Focus::focus(self.patstmt) }
}

///|
impl[A : Focus] Focus for Array[A] with focus(self) {
  self.map(Focus::focus)
}

///|
impl Focus for Producer with focus(self) {
  match self {
    Var(_) | Lit(_) => self
    Mu(x, s) => Mu(x, Focus::focus(s))
    MuDyn(x, s) => MuDyn(x, Focus::focus(s))
    Cocase(cocases) => Cocase(Focus::focus(cocases))
    Constructor(ct, pargs, cargs) =>
      match pargs.search_by(x => not(Producer::is_value(x))) {
        None => Constructor(ct, Focus::focus(pargs), Focus::focus(cargs))
        Some(p) => {
          let v = fresh_var([self])
          let cv = fresh_covar([self])
          let p = pargs[p]
          let new_args = pargs.map(p1 => if p1 == p { Var(v) } else { p1 })
          Mu(
            cv,
            Cut(
              Focus::focus(p),
              MuTilde(
                v,
                Cut(Focus::focus(Constructor(ct, new_args, cargs)), Covar(cv)),
              ),
            ),
          )
        }
      }
  }
}

///|
impl Focus for Consumer with focus(self) {
  match self {
    Covar(x) => Covar(x)
    MuTilde(x, s) => MuTilde(x, Focus::focus(s))
    MuTildeDyn(x, s) => MuTildeDyn(x, Focus::focus(s))
    Case(cases) => Case(Focus::focus(cases))
    Destructor(dt, pargs, cargs) =>
      match pargs.search_by(x => not(Producer::is_value(x))) {
        None => Destructor(dt, Focus::focus(pargs), Focus::focus(cargs))
        Some(p) => {
          let v1 = fresh_var([self])
          let v2 = fresh_var_from([self], Set::singleton(v1))
          let c = pargs[p]
          let new_args = pargs.map(c1 => if c1 == c { Var(v1) } else { c1 })
          MuTilde(
            v2,
            Cut(
              Focus::focus(c),
              MuTilde(
                v1,
                Cut(Var(v2), Focus::focus(Destructor(dt, new_args, cargs))),
              ),
            ),
          )
        }
      }
  }
}

///|
impl Focus for Statement with focus(self) {
  match self {
    Cut(p, c) => Cut(Focus::focus(p), Focus::focus(c))
    Op(p1, op, p2, c) if p1.is_value() && p2.is_value() =>
      Op(Focus::focus(p1), op, Focus::focus(p2), Focus::focus(c))
    Op(p1, op, p2, c) => {
      let v = fresh_var([self])
      if p1.is_value() {
        Cut(Focus::focus(p2), MuTilde(v, Focus::focus(Op(p1, op, Var(v), c))))
      } else {
        Cut(Focus::focus(p1), MuTilde(v, Focus::focus(Op(Var(v), op, p2, c))))
      }
    }
    IfZ(p, s1, s2) if p.is_value() =>
      IfZ(Focus::focus(p), Focus::focus(s1), Focus::focus(s2))
    IfZ(p, s1, s2) => {
      let v = fresh_var([self])
      Cut(Focus::focus(p), MuTilde(v, Focus::focus(IfZ(Var(v), s1, s2))))
    }
    Fun(nm, pargs, cargs) =>
      match pargs.search_by(x => not(Producer::is_value(x))) {
        None => Fun(nm, Focus::focus(pargs), Focus::focus(cargs))
        Some(p) => {
          let v = fresh_var([self])
          let p = pargs[p]
          let new_args = pargs.map(p1 => if p1 == p { Var(v) } else { p1 })
          Cut(
            Focus::focus(p),
            MuTilde(v, Focus::focus(Fun(nm, new_args, cargs))),
          )
        }
      }
    Done => Done
  }
}

///|
impl[A] Focus for Def[A] with focus(self) {
  { ..self, body: Focus::focus(self.body) }
}

///|
impl[A] Focus for Program[A] with focus(self) {
  { defs: self.defs.map(Focus::focus) }
}
