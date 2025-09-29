///|
pub(all) enum CoVar {
  Star
  CoVar(Int)
} derive(Eq)

///|
pub(all) struct Name(String) derive(Eq)

///|
impl Show for Name with to_string(self) {
  self.inner()
}

///|
impl Show for Name with output(self, l) {
  l.write_string(self.to_string())
}

///|
impl Show for CoVar with to_string(self) {
  match self {
    Star => "★"
    CoVar(i) => (Char::to_int('α') + i).unsafe_to_char().to_string()
  }
}

///|
impl Show for CoVar with output(self, l) {
  l.write_string(self.to_string())
}

///|
pub(all) struct Var(Int) derive(Eq)

///|
impl Show for Var with to_string(self) {
  let idx = self.inner()
  if idx < 3 {
    (Char::to_int('x') + self.inner()).unsafe_to_char().to_string()
  } else {
    let idx = idx - 3
    (Char::to_int('a') + idx).unsafe_to_char().to_string()
  }
}

///|
impl Show for Var with output(self, l) {
  l.write_string(self.to_string())
}

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
pub(all) enum TermProgram {
  Empty
  Cons(TermDef, TermProgram)
}

///|
pub(all) enum TermDef {
  Define(Name, Array[Var], Array[CoVar], Term)
}

///|
pub(all) enum Term {
  TVar(Var)
  TLiteral(Int)
  TOp(Op, Term, Term)
  TIfZero(Term, Term, Term)
  TLetIn(Var, Term, Term)
  TApply(Name, Array[Term], Array[CoVar])
} derive(Eq, Show)

///|
pub(all) enum Value {
  VInt(Int)
} derive(Eq, Show)

///|
suberror EvalError {
  NonGroundTerm
  DefNotFound(Name)
  ArityMismatch(Name, Int, Int)
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
