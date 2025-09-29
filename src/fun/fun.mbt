///|
pub(all) enum CoVar {
  Star
  CoVar(Int)
} derive(Eq)

///|
impl Show for CoVar with to_string(self) {
  match self {
    Star => "★"
    CoVar(i) => "α" + i.to_string()
  }
}

///|
impl Show for CoVar with output(self, l) {
  l.write_string(self.to_string())
}

///|
pub(all) struct Var(Int) derive(Eq, Show)

///|
let global_var : Ref[Int] = @ref.new(0)

///|
pub fn fresh() -> Int {
  let v = global_var.val
  global_var.update(x => x + 1)
  v
}

///|
pub(all) enum Op {
  Add
  Sub
  Times
} derive(Eq)

///|
pub fn compute(self : Op, v1 : Int, v2 : Int) -> Int {
  match self {
    Add => v1 + v2
    Sub => v1 - v2
    Times => v1 * v2
  }
}

///|
pub(all) enum Term {
  TVar(Var)
  TLiteral(Int)
  TOp(Op, Term, Term)
  TIfZero(Term, Term, Term)
} derive(Eq, Show)

///|
pub(all) enum Value {
  VInt(Int)
} derive(Eq, Show)

///|
suberror EvalError {
  NonGroundTerm
}

///|
pub fn eval(self : Term) -> Value raise EvalError {
  match self {
    TIfZero(TLiteral(0), t1, _) => t1.eval()
    TIfZero(TLiteral(_), _, t2) => t2.eval()
    TOp(op, TLiteral(v1), TLiteral(v2)) => VInt(op.compute(v1, v2))
    _ => raise NonGroundTerm
  }
}
