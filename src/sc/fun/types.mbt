///|
struct TyVar(String) derive(Eq)

///|
pub(all) enum Ty {
  TyVar(TyVar)
  IntTy
  ListTy(Ty)
  StreamTy(Ty)
  PairTy(Ty, Ty)
  LPairTy(Ty, Ty) // lazy pair
  FunTy(Ty, Ty)
} derive(Eq)

///|
impl Show for Ty with to_string(self) {
  match self {
    TyVar(v) => v.inner()
    IntTy => "Int"
    ListTy(ty) => "[\{ty}]"
    StreamTy(ty) => "Stream\{ty}"
    PairTy(t1, t2) => "Pair(\{t1}, \{t2})"
    LPairTy(t1, t2) => "LPair(\{t1}, \{t2})"
    FunTy(t1, t2) => "\{t1} -> \{t2}"
  }
}

///|
impl Show for Ty with output(self, logger) {
  logger.write_string(self.to_string())
}
