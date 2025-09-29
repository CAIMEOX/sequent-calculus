///|
typealias @fun.Term

///|
typealias @core.Producer

///|
typealias @immut/sorted_set.SortedSet as ISet

///|
fn elaborate_op(self : @fun.BinOp) -> @core.BinOp {
  match self {
    Sum => @core.Add
    Sub => @core.Sub
    Prod => @core.Mul
  }
}

///|
fn elaborate_ctor(self : @fun.Ctor) -> @core.Ctor {
  match self {
    Nil => @core.Nil
    Cons => @core.Cons
    Tup => @core.Tup
  }
}

///|
fn elaborate_dtor(self : @fun.Dtor) -> @core.Dtor {
  match self {
    Hd => @core.Head
    Tl => @core.Tail
    Fst => @core.Fst
    Snd => @core.Snd
    Ap => abort("Ap destructor cannot be elaborated")
  }
}

///|
pub fn elaborate(t : Term) -> (Producer, Set[String]) {
  let state = Set::new()
  letrec go: (Term) -> Producer = term => match term {
    VarT(v) => Var(v)
    Lit(n) => Lit(n)
    Op(t1, op, t2) => {
      let t1p = go(t1)
      let t2p = go(t2)
      let alpha = @core.fresh_covar_from(
        [t1p, t2p],
        state.iter() |> ISet::from_iter,
      )
      state.add(alpha)
      Mu(alpha, Op(t1p, op.elaborate_op(), t2p, Covar(alpha)))
    }
    IfZ(t1, t2, t3) => {
      let t1p = go(t1)
      let t2p = go(t2)
      let t3p = go(t3)
      let alpha = @core.fresh_covar_from(
        [t1p, t2p, t3p],
        state.iter() |> ISet::from_iter,
      )
      state.add(alpha)
      Mu(alpha, IfZ(t1p, Cut(t2p, Covar(alpha)), Cut(t3p, Covar(alpha))))
    }
    Let(v, t1, t2) => {
      let t1p = go(t1)
      let t2p = go(t2)
      let alpha = @core.fresh_covar_from(
        [t1p, t2p],
        state.iter() |> ISet::from_iter,
      )
      state.add(alpha)
      Mu(alpha, Cut(t1p, MuTildeDyn(v, Cut(t2p, Covar(alpha)))))
    }
    Constructor(ct, ctargs) => {
      let ctargsp = ctargs.map(go)
      Constructor(ct.elaborate_ctor(), ctargsp, [])
    }
    Destructor(t, dt, args) => {
      let tp = go(t)
      let argsp = args.map(go)
      let alpha = @core.fresh_covar_from(
        [tp, ..argsp],
        state.iter() |> ISet::from_iter,
      )
      state.add(alpha)
      Mu(alpha, Cut(tp, Destructor(dt.elaborate_dtor(), argsp, [Covar(alpha)])))
    }
    Case(ts, clauses) => {
      let tsp = go(ts)
      let rhss = clauses.map(cl => go(cl.body))
      let alpha = @core.fresh_covar_from(
        [tsp, ..rhss],
        state.iter() |> ISet::from_iter,
      )
      state.add(alpha)
      let rhssp = rhss.map(p => @core.Cut(p, @core.Covar(alpha)))
      let pts = clauses
        .zip(rhssp)
        .map(pair => {
          let (cls, c) = pair
          (
            {
              xtor: cls.ctor.elaborate_ctor(),
              patvars: cls.vars,
              patcovars: [],
              patstmt: c,
            } : @core.Pattern[@core.Ctor])
        })
      Mu(alpha, Cut(tsp, Case(pts)))
    }
    Cocase(patterns) =>
      Cocase(
        patterns.map(cls => {
          let { body, vars, ctor } = cls
          let tp = go(body)
          let alpha = @core.fresh_covar_from(
            [tp],
            state.iter() |> ISet::from_iter,
          )
          state.add(alpha)
          {
            xtor: ctor.elaborate_dtor(),
            patvars: vars,
            patcovars: [alpha],
            patstmt: Cut(tp, Covar(alpha)),
          }
        }),
      )
    Lam(x, t) => {
      let t1p = go(t)
      let alpha = @core.fresh_covar_from([t1p], state.iter() |> ISet::from_iter)
      state.add(alpha)
      Cocase([
        {
          xtor: @core.Ap,
          patvars: [x],
          patcovars: [alpha],
          patstmt: Cut(t1p, Covar(alpha)),
        },
      ])
    }
    App(t1, t2) => {
      let t1p = go(t1)
      let t2p = go(t2)
      let alpha = @core.fresh_covar_from(
        [t1p, t2p],
        state.iter() |> ISet::from_iter,
      )
      state.add(alpha)
      Mu(alpha, Cut(t1p, Destructor(@core.Ap, [t2p], [Covar(alpha)])))
    }
    Fun(name, prod_args, covar_args) => {
      let prod_args_p = prod_args.map(go)
      let covar_args_p = covar_args.map(cv => @core.Covar(cv))
      let used_covars = state.iter() |> ISet::from_iter
      let covar_set = ISet::from_array(covar_args)
      let all_used = used_covars.union(covar_set)
      let alpha = @core.fresh_covar_from(prod_args_p, all_used)
      state.add(alpha)
      Mu(alpha, @core.Fun(name, prod_args_p, covar_args_p))
    }
    Goto(t, alpha) => {
      let tp = go(t)
      let beta = @core.fresh_covar_from(
        [tp],
        state.iter() |> ISet::from_iter |> ISet::add(alpha),
      )
      state.add(beta)
      MuDyn(beta, Cut(tp, Covar(alpha)))
    }
    Label(alpha, t) => {
      state.add(alpha)
      let tp = go(t)
      MuDyn(alpha, Cut(tp, Covar(alpha)))
    }
  }

  (go(t), state)
}

///|
pub fn[Ty] elaborate_def(def : @fun.Def[Ty]) -> @core.Def[Ty] {
  let (body_p, used_covars) = elaborate(def.body)
  let cv_fresh = @core.fresh_covar_from(
    [body_p],
    used_covars.iter() |> ISet::from_iter,
  )
  let new_cut = @core.Cut(body_p, @core.Covar(cv_fresh))
  @core.Def::{
    name: def.name,
    pargs: def.args,
    cargs: def.cont + [(cv_fresh, def.ret_ty)],
    body: new_cut,
  }
}

///|
/// Compile a program of the surface language Fun to a program of the intermediate language Core.
pub fn[Ty] elaborate_program(prog : @fun.Program[Ty]) -> @core.Program[Ty] {
  @core.Program::{ defs: prog.defs.map(elaborate_def) }
}
