///|
pub(open) trait FreeV {
  free_vars(Self) -> Set[Var]
  free_covars(Self) -> Set[Covar]
}

///|
pub impl[A : FreeV] FreeV for Array[A] with free_vars(xs) {
  xs.map(x => x.free_vars()).fold(init=Set::new(), Set::union)
}

///|
pub impl[A : FreeV] FreeV for Array[A] with free_covars(xs) {
  xs.map(x => x.free_covars()).fold(init=Set::new(), Set::union)
}

///|
pub typealias &FreeV as Free

///|
fn[A : FreeV] fresh_vars_from(xs : Array[A], s : Set[Var]) -> Iter[Var] {
  let fvs = FreeV::free_vars(xs).union(s)
  Iter::new(fn(yield_) {
    let mut i = 0
    while true {
      let v = "x" + i.to_string()
      i = i + 1
      if !fvs.contains(v) {
        if yield_(v) is IterEnd {
          break IterEnd
        }
      }
    } else {
      IterContinue
    }
  })
}

///|
fn[A : FreeV] fresh_vars(xs : Array[A]) -> Iter[Var] {
  fresh_vars_from(xs, Set::new())
}

///|
impl Subst with subst_covar(c, cv, self) {
  Subst::subst_sim([], [(c, cv)], self)
}

///|
pub impl FreeV for Producer with free_vars(self) {
  match self {
    Var(v) => Set::singleton(v)
    Lit(_) => Set::new()
    // mu binds a covariable, so this can be ignored
    Mu(_, s) => FreeV::free_vars(s)
    MuDyn(_, s) => FreeV::free_vars(s)
    Constructor(_, p_args, c_args) =>
      FreeV::free_vars(p_args).union(FreeV::free_vars(c_args))
    Cocase(pts) => FreeV::free_vars(pts)
  }
}

///|
pub impl FreeV for Producer with free_covars(self) {
  match self {
    Var(_) => Set::new()
    Lit(_) => Set::new()
    Mu(cv, st) => FreeV::free_covars(st).remove(cv)
    MuDyn(cv, st) => FreeV::free_covars(st).remove(cv)
    Constructor(_, p_args, c_args) =>
      FreeV::free_covars(p_args).union(FreeV::free_covars(c_args))
    Cocase(pts) => FreeV::free_covars(pts)
  }
}

///|
pub impl FreeV for Consumer with free_vars(self) {
  match self {
    Covar(_) => Set::new()
    MuTilde(v, st) => FreeV::free_vars(st).remove(v)
    MuTildeDyn(v, st) => FreeV::free_vars(st).remove(v)
    Case(pts) => FreeV::free_vars(pts)
    Destructor(_, p_args, c_args) =>
      FreeV::free_vars(p_args).union(FreeV::free_vars(c_args))
  }
}

///|
pub impl FreeV for Consumer with free_covars(self) {
  match self {
    Covar(cv) => Set::singleton(cv)
    // mutilde binds a variable, so this variable can be ignored
    MuTilde(_, st) => FreeV::free_covars(st)
    MuTildeDyn(_, st) => FreeV::free_covars(st)
    Case(pts) => FreeV::free_covars(pts)
    Destructor(_, p_args, c_args) =>
      FreeV::free_covars(p_args).union(FreeV::free_covars(c_args))
  }
}

///|
pub impl FreeV for Statement with free_vars(self) {
  match self {
    Cut(p, c) => FreeV::free_vars(p).union(FreeV::free_vars(c))
    Op(p1, _, p2, c) =>
      FreeV::free_vars(p1)
      .union(FreeV::free_vars(p2))
      .union(FreeV::free_vars(c))
    IfZ(p, s1, s2) =>
      FreeV::free_vars(p)
      .union(FreeV::free_vars(s1))
      .union(FreeV::free_vars(s2))
    Fun(_, p_args, c_args) =>
      FreeV::free_vars(p_args).union(FreeV::free_vars(c_args))
    Done => Set::new()
  }
}

///|
pub impl FreeV for Statement with free_covars(self) {
  match self {
    Cut(p, c) => FreeV::free_covars(p).union(FreeV::free_covars(c))
    Op(p1, _, p2, c) =>
      FreeV::free_covars(p1)
      .union(FreeV::free_covars(p2))
      .union(FreeV::free_covars(c))
    IfZ(p, s1, s2) =>
      FreeV::free_covars(p)
      .union(FreeV::free_covars(s1))
      .union(FreeV::free_covars(s2))
    Fun(_, p_args, c_args) =>
      FreeV::free_covars(p_args).union(FreeV::free_covars(c_args))
    Done => Set::new()
  }
}

///|
impl[A] FreeV for Pattern[A] with free_vars(self) {
  let vars_set = Set::from_array(self.patvars)
  FreeV::free_vars(self.patstmt).difference(vars_set)
}

///|
impl[A] FreeV for Pattern[A] with free_covars(self) {
  let cvars_set = Set::from_array(self.patcovars)
  FreeV::free_covars(self.patstmt).difference(cvars_set)
}

///|
pub fn[A : FreeV] fresh_covar(xs : Array[A]) -> Covar {
  fresh_covars(xs).take(1).collect()[0]
}

///|
pub fn[A : FreeV] fresh_covar_from(xs : Array[A], s : Set[Covar]) -> Covar {
  fresh_covars(xs).filter(cv => not(s.contains(cv))).take(1).collect()[0]
}

///|
pub fn[A : FreeV] fresh_var(xs : Array[A]) -> Var {
  fresh_vars(xs).take(1).collect()[0]
}

///|
pub fn[A : FreeV] fresh_var_from(xs : Array[A], s : Set[Var]) -> Var {
  fresh_vars_from(xs, s).take(1).collect()[0]
}

///|
pub fn[A : FreeV] fresh_covars(xs : Array[A]) -> Iter[Covar] {
  let fvs = FreeV::free_covars(xs)
  Iter::new(fn(yield_) {
    let mut i = 0
    while true {
      let cv = "a" + i.to_string()
      i = i + 1
      if !fvs.contains(cv) {
        if yield_(cv) is IterEnd {
          break IterEnd
        }
      }
    } else {
      IterContinue
    }
  })
}
