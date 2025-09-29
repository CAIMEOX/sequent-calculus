///|
typealias String as Var

///|
typealias String as Covar

///|
pub(all) enum Ctor {
  Nil
  Cons
  Tup
} derive(Eq)

///|
pub(all) struct Pattern[A] {
  xtor : A
  patvars : Array[Var]
  patcovars : Array[Covar]
  patstmt : Statement
} derive(Eq)

///|
pub(all) enum Producer {
  Var(Var)
  Lit(Int)
  Mu(Covar, Statement)
  MuDyn(Covar, Statement)
  Constructor(Ctor, Array[Producer], Array[Consumer])
  Cocase(Array[Pattern[Dtor]])
} derive(Eq)

///|
pub(all) enum BinOp {
  Add
  Sub
  Mul
  Div
} derive(Eq)

///|
pub(all) enum Dtor {
  Fst
  Snd
  Head
  Tail
  Ap
} derive(Eq)

///|
pub(all) enum Consumer {
  Covar(Covar)
  MuTilde(Var, Statement)
  MuTildeDyn(Var, Statement)
  Case(Array[Pattern[Ctor]])
  Destructor(Dtor, Array[Producer], Array[Consumer])
} derive(Eq)

///|
pub(all) enum Statement {
  Cut(Producer, Consumer)
  Op(Producer, BinOp, Producer, Consumer)
  IfZ(Producer, Statement, Statement)
  Fun(String, Array[Producer], Array[Consumer]) // Using String for Name
  Done
} derive(Eq)

// Top-level Definitions (Definition 2.4)

///|
pub(all) struct Def[A] {
  name : String
  pargs : Array[(Var, A)]
  cargs : Array[(Covar, A)]
  body : Statement
} derive(Eq)

///|
pub(all) struct Program[A] {
  defs : Array[Def[A]]
} derive(Eq)
