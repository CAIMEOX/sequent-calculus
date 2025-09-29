///|
typealias @immut/sorted_set.SortedSet as Set

///|
pub(open) trait Subst {
  subst_sim(Array[(Producer, Var)], Array[(Consumer, Covar)], Self) -> Self
  subst_var(Producer, Var, Self) -> Self = _
  subst_covar(Consumer, Covar, Self) -> Self = _
}

///|
impl Subst with subst_var(p, v, self) {
  Subst::subst_sim([(p, v)], [], self)
}

///|
impl[A : Subst] Subst for Array[A] with subst_sim(ps, cs, xs) {
  xs.map(x => Subst::subst_sim(ps, cs, x))
}

///|
impl[A] Subst for Pattern[A] with subst_sim(ps, cs, self) {
  let producers : Array[Free] = ps.map(p => p.0)
  let producer_vars : Array[Free] = ps.map(p => Var(p.1))
  let consumers : Array[Free] = cs.map(p => p.0)
  let consumer_vars : Array[Free] = cs.map(p => Covar(p.1))
  let all_free : Array[Free] = [
      self.patstmt,
      ..producer_vars,
      ..producers,
      ..consumer_vars,
      ..consumers,
    ]
  let fresh_vars_list = fresh_vars(all_free)
    .take(self.patvars.length())
    .collect()
  let fresh_covars_list = fresh_covars(all_free)
    .take(self.patcovars.length())
    .collect()
  let var_pairs = fresh_vars_list.mapi(fn(i, v) { (Var(v), self.patvars[i]) })
  let covar_pairs = fresh_covars_list.mapi(fn(i, cv) {
    (Covar(cv), self.patcovars[i])
  })
  let st_renamed = Subst::subst_sim(var_pairs, covar_pairs, self.patstmt)
  let st_final = Subst::subst_sim(ps, cs, st_renamed)
  Pattern::{
    xtor: self.xtor,
    patvars: fresh_vars_list,
    patcovars: fresh_covars_list,
    patstmt: st_final,
  }
}

///|
impl Subst for Producer with subst_sim(ps, cs, self) {
  match self {
    Var(v) =>
      ps.search_by(pair => pair.1 == v).map(x => ps[x].0).unwrap_or(Var(v))
    Lit(n) => Lit(n)
    Mu(cv, st) => {
      let consumers : Array[Free] = cs.map(p => p.0)
      let consumer_vars : Array[Free] = cs.map(p => Covar(p.1))
      let producers : Array[Free] = ps.map(p => p.0)
      let all_free : Array[Free] = [
          st, ..consumer_vars, ..consumers, ..producers,
        ]
      let cv_fresh = fresh_covar(all_free)
      let st_renamed = Subst::subst_covar(Covar(cv_fresh), cv, st)
      Mu(cv_fresh, Subst::subst_sim(ps, cs, st_renamed))
    }
    MuDyn(cv, st) => {
      let consumers : Array[Free] = cs.map(p => p.0)
      let consumer_vars : Array[Free] = cs.map(p => Covar(p.1))
      let producers : Array[Free] = ps.map(p => p.0)
      let all_free : Array[&FreeV] = [
          st, ..consumer_vars, ..consumers, ..producers,
        ]
      let cv_fresh = fresh_covar(all_free)
      let st_renamed = Subst::subst_covar(Covar(cv_fresh), cv, st)
      MuDyn(cv_fresh, Subst::subst_sim(ps, cs, st_renamed))
    }
    Constructor(ct, p_args, c_args) =>
      Constructor(
        ct,
        Subst::subst_sim(ps, cs, p_args),
        Subst::subst_sim(ps, cs, c_args),
      )
    Cocase(patterns) => Cocase(Subst::subst_sim(ps, cs, patterns))
  }
}

///|
impl Subst for Consumer with subst_sim(ps, cs, self) {
  match self {
    Covar(cv) =>
      cs.search_by(pair => pair.1 == cv).map(x => cs[x].0).unwrap_or(Covar(cv))
    MuTilde(v, st) => {
      let producers : Array[Free] = ps.map(x => x.0)
      let producer_vars : Array[Free] = ps.map(x => Var(x.1))
      let consumers : Array[Free] = cs.map(x => x.0)
      let all_free : Array[Free] = [
          st, ..producer_vars, ..producers, ..consumers,
        ]
      let v_fresh = fresh_var(all_free)
      let st_renamed = Subst::subst_var(Var(v_fresh), v, st)
      MuTilde(v_fresh, Subst::subst_sim(ps, cs, st_renamed))
    }
    MuTildeDyn(v, st) => {
      let producers : Array[Free] = ps.map(x => x.0)
      let producer_vars : Array[Free] = ps.map(x => Var(x.1))
      let consumers : Array[Free] = cs.map(x => x.0)
      let all_free : Array[Free] = [
          st, ..producer_vars, ..producers, ..consumers,
        ]
      let v_fresh = fresh_var(all_free)
      let st_renamed = Subst::subst_var(Var(v_fresh), v, st)
      MuTildeDyn(v_fresh, Subst::subst_sim(ps, cs, st_renamed))
    }
    Case(patterns) => Case(Subst::subst_sim(ps, cs, patterns))
    Destructor(dt, p_args, c_args) =>
      Destructor(
        dt,
        Subst::subst_sim(ps, cs, p_args),
        Subst::subst_sim(ps, cs, c_args),
      )
  }
}

///|
impl Subst for Statement with subst_sim(ps, cs, self) {
  match self {
    Cut(p, c) => Cut(Subst::subst_sim(ps, cs, p), Subst::subst_sim(ps, cs, c))
    Op(p1, op, p2, c) =>
      Op(
        Subst::subst_sim(ps, cs, p1),
        op,
        Subst::subst_sim(ps, cs, p2),
        Subst::subst_sim(ps, cs, c),
      )
    IfZ(p, s1, s2) =>
      IfZ(
        Subst::subst_sim(ps, cs, p),
        Subst::subst_sim(ps, cs, s1),
        Subst::subst_sim(ps, cs, s2),
      )
    Fun(nm, p_args, c_args) =>
      Fun(
        nm,
        Subst::subst_sim(ps, cs, p_args),
        Subst::subst_sim(ps, cs, c_args),
      )
    Done => Done
  }
}
