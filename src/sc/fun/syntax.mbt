///|
typealias String as Var

///|
typealias String as Covar

///|
typealias String as Name

///|
pub(all) enum Ctor {
  Nil
  Cons
  Tup
} derive(Show, Eq)

///|
pub(all) enum Dtor {
  Hd
  Tl
  Fst
  Snd
  Ap
} derive(Show, Eq)

///|
pub(all) enum BinOp {
  Prod
  Sum
  Sub
} derive(Show, Eq)

///|
pub(all) struct Clause[A] {
  ctor : A
  vars : Array[Var]
  body : Term
} derive(Show, Eq)

///|
pub(all) enum Term {
  VarT(Var)
  Lit(Int)
  Op(Term, BinOp, Term)
  IfZ(Term, Term, Term)
  Let(Var, Term, Term)
  Fun(Name, Array[Term], Array[Covar])
  Constructor(Ctor, Array[Term])
  Destructor(Term, Dtor, Array[Term])
  Case(Term, Array[Clause[Ctor]])
  Cocase(Array[Clause[Dtor]])
  Lam(Var, Term)
  App(Term, Term)
  Goto(Term, Covar)
  Label(Covar, Term)
} derive(Show, Eq)

///|
pub(all) struct Def[Ty] {
  name : Name
  args : Array[(Var, Ty)]
  cont : Array[(Covar, Ty)]
  body : Term
  ret_ty : Ty
} derive(Show, Eq)

///|
pub(all) struct Program[Ty] {
  defs : Array[Def[Ty]]
} derive(Show, Eq)
