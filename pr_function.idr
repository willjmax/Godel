import Data.Fin
import Data.Vect

data PR : Nat -> Type where
  Const : Nat -> PR n
  Succ  : PR (S Z)
  Proj  : (n : Nat) -> (k : Fin n) -> PR n
  Comp  : PR n -> Vect n (PR k) -> PR k
  Rec   : PR k -> PR (S (S k)) -> PR (S k)

eval : PR n -> Vect n Nat -> Nat
eval (Const k) _           = k
eval Succ xs               = S (index 0 xs)
eval (Proj _ k) xs         = index k xs
eval (Comp f gs) xs        = eval f (map (\g => eval g xs) gs)
eval (Rec psi _) (Z :: xs) = eval psi xs
eval phi@(Rec _ theta) (S k :: xs) =
  eval theta (k :: (eval phi (k :: xs)) :: xs)

add : PR 2
add = Rec (Proj 1 0) (Comp Succ [Proj 3 1])

mul : PR 2
mul = Rec (Const 0) (Comp add [Proj 3 1, Proj 3 2])

exp : PR 2
exp = Rec (Const 1) (Comp mul [Proj 3 1, Proj 3 2])

neg : PR 1
neg = Rec (Comp Succ [Const 0]) (Const 0)

or : PR 2
or = Rec (Const 0) (Comp neg [Comp neg [Proj 3 2]])

and : PR 2
and = Comp neg [Comp or [Comp neg [Proj 2 0], Comp neg [Proj 2 1]]]

pred : PR 1
pred = Rec (Const 0) (Proj 2 0)

sub : PR 2
sub = Rec (Proj 1 0) (Comp pred [Proj 3 1])

equals : PR 2
equals = Comp and [sub, Comp sub [Proj 2 1, Proj 2 0]]

projections : (n : Nat) -> Vect n (PR n)
projections n = map (\k => Proj n k) (allFins n)

prod : {n : Nat} -> PR (S n) -> PR (S n)
prod rho = Rec base rec where
  base = Comp rho (Const 0 :: projections n)
  rec  = Comp mul [Proj (S (S n)) 1, Comp rho (Comp Succ [Proj (S (S n)) 0] :: drop 2 (projections (S (S n))))]

sum : {n : Nat} -> PR (S n) -> PR (S n)
sum rho = Rec base rec where
  base = Comp rho (Const 0 :: projections n)
  rec  = Comp add [Proj (S (S n)) 1, Comp rho (Comp Succ [Proj (S (S n)) 0] :: drop 2 (projections (S (S n))))]

cast : PR n -> PR n
cast phi = Comp neg [Comp neg [phi]]

leq : PR 2
leq = cast (Comp sub [Proj 2 1, Proj 2 0])

geq : PR 2
geq = cast (Comp sub [Proj 2 0, Proj 2 1])

lt : PR 2
lt = Comp neg [geq]

gt : PR 2
gt = Comp neg [leq]

exists : {n : Nat} -> {m : Nat} -> PR n -> PR (S m) -> PR (n + m)
exists phi rho = Comp (prod rho) (f :: fs) where
  f  : PR (n + m)
  fs : Vect m (PR (n + m))
  f  = Comp phi (take n (projections (n + m)))
  fs = drop n (projections (n + m))

forAll : {n : Nat} -> {m : Nat} -> PR n -> PR (S m) -> PR (n + m)
forAll phi rho = Comp neg [exists phi not_rho] where
  not_rho : PR (S m)
  not_rho = Comp neg [rho]

mu : {n : Nat} -> {m : Nat} -> PR n -> PR (S m) -> PR (n + m)
mu phi rho = Comp (sum (prod rho)) (f :: fs) where
  f  : PR (n + m)
  fs : Vect m (PR (n + m))
  f  = Comp phi (take n (projections (n + m)))
  fs = drop n (projections (n + m))
