import Decidable.Equality

data Order : Type where
  Constant  : Order
  Predicate : Order -> Order

predInjective : Predicate x = Predicate y -> x = y
predInjective Refl = Refl

predNotConst : (order : Order) -> (Predicate order) = Constant -> Void
predNotConst Constant () impossible
predNotConst (Predicate order) () impossible

constNotPred : (order : Order) -> Constant = (Predicate order) -> Void
constNotPred Constant () impossible
constNotPred (Predicate order) () impossible

DecEq Order where
  decEq Constant Constant = Yes Refl
  decEq (Predicate x) (Predicate y) =
    case decEq x y of
         Yes p => Yes (cong Predicate p)
         No contra => No (\p => contra (predInjective p))
  decEq Constant (Predicate x) = No (constNotPred x)
  decEq (Predicate x) Constant = No (predNotConst x)

orderEq : Order -> Order -> Bool
orderEq Constant Constant           = True
orderEq (Predicate x) (Predicate y) = orderEq x y
orderEq _ _                         = False

data Var : Order -> Type where
  V : Nat -> Var order

getNat : Var order -> Nat
getNat (V x) = x

sameVar : {o1 : Order} -> {o2 : Order} -> Var o1 -> Var o2 -> Bool
sameVar {o1} {o2} (V x) (V y) = (orderEq o1 o2) && (x == y)

liftVar : Var order -> Var (Predicate order)
liftVar (V x) = V x

data Expr : Order -> Type where
  Zero : Expr Constant
  Succ : Expr Constant -> Expr Constant
  ExpN : Var order -> Expr order

data VarIn : Var order -> Expr order -> Type where
  IsVar : (v : Var order) -> VarIn v (ExpN v)

toNat : Expr order -> Nat
toNat Zero       = Z
toNat (Succ e)   = S (toNat e)
toNat (ExpN v)   = getNat v

liftExpr : Expr order -> Expr (Predicate order)
liftExpr Zero     = ExpN (V Z)
liftExpr (Succ e) = ExpN (V (S (toNat e)))
liftExpr (ExpN v) = ExpN (V (S (getNat v)))

subExpr : {o1 : Order} -> {o2 : Order} -> 
          Expr o1 -> Var o2 -> Expr o2 -> Expr o1
subExpr (ExpN v1) v2 e =
  case decEq o1 o2 of
       Yes p => if sameVar v1 v2 then rewrite p in e else ExpN v1
       No _ => ExpN v1
subExpr e _ _ = e

data Formula : Type where
  App    : {order : Order} -> Expr (Predicate order) -> Expr order -> Formula
  Or     : Formula -> Formula -> Formula
  Not    : Formula -> Formula
  ForAll : {order : Order} -> Var order -> Formula -> Formula

--do not implement godel numbering, just define the type signature
godelNum : Formula -> Nat

data FreeIn : Var order -> Formula -> Type where
  FreeAppL   : (el : Expr (Predicate order)) -> (er : Expr order) -> 
               VarIn v el -> FreeIn v (App el er)
  FreeAppR   : (el : Expr (Predicate order)) -> (er : Expr order) ->
               VarIn v er -> FreeIn v (App el er)
  FreeOr     : FreeIn v a -> FreeIn v b -> FreeIn v (Or a b)
  FreeNot    : FreeIn v a -> FreeIn v (Not a)
  FreeForAll : FreeIn v a -> (u : Var order) -> Not (v = u) -> FreeIn v (ForAll u a)

data BoundIn : Var order -> Formula -> Type where
  BoundAppL   : (el : Expr (Predicate order)) -> (er : Expr order) ->
                VarIn v el -> BoundIn v (ForAll v (App el er))
  BoundAppR   : (el : Expr (Predicate order)) -> (er : Expr order) ->
                VarIn v er -> BoundIn v (ForAll v (App el er))
  BoundOr     : (a : Formula) -> (b : Formula) -> BoundIn v a -> BoundIn v (Or a b)
  BoundNot    : (a : Formula) -> BoundIn v a -> BoundIn v (Not a)
  BoundForAll : (a : Formula) -> BoundIn v a -> (u : Var order) -> BoundIn v (ForAll u a)

data Collision : Formula -> Var order -> Expr order -> Type where
  Col : (a : Formula) -> BoundIn v a -> FreeIn u a -> Collision a u (ExpN v)

typeLift : Formula -> Formula
typeLift (App e1 e2)  = App (liftExpr e1) (liftExpr e2)
typeLift (Or a b)     = Or (typeLift a) (typeLift b)
typeLift (Not a)      = Not (typeLift a)
typeLift (ForAll v a) = ForAll (liftVar v) (typeLift a)

substitute : {o1 : Order} -> Formula -> Var o1 -> Expr o1 -> Formula
substitute (App e1 e2) v e = App (subExpr e1 v e) (subExpr e2 v e)
substitute (Or a b) v e    = Or (substitute a v e) (substitute b v e)
substitute (Not a) v e     = Not (substitute a v e)
substitute {o1} (ForAll {order} x a) v e = 
  if sameVar {o1=order} {o2=o1} x v 
  then ForAll x a 
  else ForAll x (substitute a v e)

and : Formula -> Formula -> Formula
and a b = Not (Or (Not a) (Not b))

implies : Formula -> Formula -> Formula
implies a b = Or (Not a) b

iff : Formula -> Formula -> Formula
iff a b = and (implies a b) (implies b a)

exists : {order : Order} -> Var order -> Formula -> Formula
exists x a = Not (ForAll x (Not a))

equals : {order : Order} -> Expr order -> Expr order -> Formula
equals x y = 
  ForAll predicate (implies (App (ExpN predicate) x) 
                            (App (ExpN predicate) y))
  where
    predicate : Var (Predicate order)
    predicate = V Z

data PAxiom : Formula -> Type where
  SuccNotZero : (x : Expr Constant) -> PAxiom (Not (equals (Succ x) Zero))

  SuccInjective : (x : Expr Constant) -> (y : Expr Constant) -> 
                  PAxiom (implies (equals (Succ x) (Succ y)) (equals (Succ x) (Succ y)))

  Induction : (f : Expr (Predicate Constant)) -> (x : Var Constant) ->
              PAxiom (implies (and (App f Zero)
                                  (ForAll x (implies (App f (ExpN x)) 
                                                     (App f (Succ (ExpN x))))))
                              (ForAll x (App f (ExpN x))))
                               
  PorP  : (p : Formula) -> PAxiom (implies (Or p p) p)
  Intro : (p : Formula) -> (q : Formula) -> PAxiom (implies p (Or p q))
  OrSym : (p : Formula) -> (q : Formula) -> PAxiom (implies (Or p q) (Or q p))

  ImpIntro : (p : Formula) -> (q : Formula) -> (r : Formula) ->
             PAxiom (implies (implies p q)
                            (implies (Or r p) (Or r q)))

  ForAllSub : (a : Formula) -> (v : Var order) -> (e : Expr order) -> 
              Not (Collision a v e) ->
              PAxiom (implies (ForAll v a) (substitute a v e))

  ForAllOr : (v : Var order) -> (b : Formula) -> (a : Formula) -> Not (FreeIn v b) ->
             PAxiom (implies (ForAll v (Or b a))
                            (Or b (ForAll v a)))

  Reduce : (v : Var order) -> (u : Var (Predicate order)) -> (a : Formula) ->
           Not (FreeIn u a) ->
           PAxiom (exists u 
                         (iff (ForAll v (App (ExpN u) (ExpN v)))
                              a))

  ClassEq : (x1 : Var order) -> (x2 : Var (Predicate order)) -> (y2 : Var (Predicate order)) ->
            PAxiom (implies (iff (ForAll x1 (App (ExpN x2) (ExpN x1)))
                                (App (ExpN y2) (ExpN x1)))
                           (equals (ExpN x2) (ExpN y2)))

data Proof : Formula -> Type where
  Axiom  : PAxiom a -> Proof a
  MP     : Proof b -> Proof (implies b c) -> Proof c
  IntroA : Proof a -> (v : Var order) -> Proof (ForAll v a)
