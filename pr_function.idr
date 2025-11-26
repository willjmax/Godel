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

ifelse : PR n -> PR n -> PR n -> PR n
ifelse cond is_true is_false = 
  Comp add [
    Comp mul [is_false, cond],
    Comp mul [is_true, Comp sub [Const 1, cond]]]

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
mu phi rho = ifelse notfound (Const 0) minimizer where
  minimizer = Comp (sum (prod rho)) (f :: fs) where
    f  : PR (n + m)
    fs : Vect m (PR (n + m))
    f  = Comp phi (take n (projections (n + m)))
    fs = drop n (projections (n + m))
  notfound = Comp equals [minimizer, Comp Succ [Comp phi (take n (projections (n + m)))]]

divides : PR 2
divides = Comp (exists bound relation) [Proj 2 1, Proj 2 0, Proj 2 1] where
  bound    : PR 1
  relation : PR 3
  bound    = Proj 1 0
  relation = Comp equals [Proj 3 2, Comp mul [Proj 3 0, Proj 3 1]]

isPrime : PR 1
isPrime = Comp and [Comp neg [Comp (exists (Proj 1 0) relation) [Proj 1 0, Proj 1 0]], gt_one] where
  gt_one : PR 1
  gt_one = Comp gt [Proj 1 0, Const 1]
  relation = Comp and [not_one, Comp and [not_x, divides]] where
    not_one   : PR 2 
    not_x     : PR 2 
    not_one   = Comp neg [Comp equals [Const 1, Proj 2 0]]
    not_x     = Comp neg [Comp equals [Proj 2 0, Proj 2 1]]

nthPrimeDiv : PR 2
nthPrimeDiv = Rec (Const 0) (Comp (mu (Proj 1 0) cond) [Proj 3 2, Proj 3 1, Proj 3 2]) where
  cond : PR 3
  cond = Comp and [divides_x, Comp and [y_is_prime, gt_prev]] where
    divides_x  = Comp divides [Proj 3 0, Proj 3 2]
    y_is_prime = Comp isPrime [Proj 3 0]
    gt_prev    = Comp gt [Proj 3 0, Proj 3 1]

fact : PR 1
fact = Rec (Const 1) (Comp mul [Comp Succ [Proj 2 0], Proj 2 1])

nthPrime : PR 1
nthPrime = Rec (Const 0) (Comp (mu bound cond) [Proj 2 1, Proj 2 0, Proj 2 1]) where
  bound : PR 1
  cond  : PR 3
  bound = Comp mul [Comp add [Proj 1 0, Const 1], Const 2]
  cond  = Comp and [y_is_prime, gt_prev] where
    y_is_prime = Comp isPrime [Proj 3 0]
    gt_prev    = Comp gt [Proj 3 0, Proj 3 2]
