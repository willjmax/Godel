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

implies : PR 2
implies = Comp or [Comp neg [Proj 2 0], Proj 2 1]

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

-- PRIMES

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

-- SEQUENCES

mem : PR 2                       -- y          n         x
mem = Comp (mu (Proj 1 0) cond) [Proj 2 1, Proj 2 0, Proj 2 1] where
  cond  : PR 3
  cond  = Comp and [y_pow_divs, Comp neg [y1_pow_divs]] where
    y_pow_divs = Comp divides [prime_div_raised_y, Proj 3 2] where
      prime_div_raised_y = Comp exp [Comp nthPrimeDiv [Proj 3 1, Proj 3 2], Proj 3 0]
    y1_pow_divs = Comp divides [prime_div_raised_y1, Proj 3 2] where
      prime_div_raised_y1 = Comp exp [Comp nthPrimeDiv [Proj 3 1, Proj 3 2], Comp Succ [Proj 3 0]]

len : PR 1                      -- y           x
len = Comp (mu (Proj 1 0) cond) [Proj 1 0, Proj 1 0] where
  cond : PR 2
  cond = Comp and [has_nth_prime, no_n1th_prime] where
    has_nth_prime = Comp gt [Comp nthPrimeDiv [Proj 2 0, Proj 2 1], Const 0]
    no_n1th_prime = Comp equals [Comp nthPrimeDiv [Comp Succ [Proj 2 0], Proj 2 1], Const 0]

concat : PR 2                    ---    z             x          y
concat = Comp (mu bound cond) [Proj 2 0, Proj 2 1, Proj 2 0, Proj 2 1] where
  bound : PR 2
  cond  : PR 3
  bound = Comp exp [Comp nthPrime [Comp add [Comp len [Proj 2 0], Comp len [Proj 2 1]]],
                    Comp add [Proj 2 0, Proj 2 1]]

  cond  = Comp and [forall1, forall2] where -- n        x         z
    forall1 = Comp (forAll bound1 cond1) [Proj 3 1, Proj 3 1, Proj 3 0] where
      bound1 : PR 1
      cond1  : PR 3
      bound1 = Comp len [Proj 1 0]
      cond1  = Comp equals [Comp mem [Proj 3 0, Proj 3 2], Comp mem [Proj 3 0, Proj 3 1]]

                                        --   n         x          y          z
    forall2 = Comp (forAll bound2 cond2) [Proj 3 2, Proj 3 1, Proj 3 2, Proj 3 0] where
      bound2 : PR 1
      cond2  : PR 4
      bound2 = Comp len [Proj 1 0]
      cond2  = Comp implies [Comp lt [Const 0, Proj 4 0],
                             Comp equals [Comp mem [Comp add [Proj 4 0, Comp len [Proj 4 1]], Proj 4 3],
                                          Comp mem [Proj 4 0, Proj 4 2]]]

seq : PR 1
seq = Comp exp [Const 2, Proj 1 0]

data SystemP : Type where
  Zero   : SystemP
  F      : SystemP
  Neg    : SystemP
  Or     : SystemP
  ForAll : SystemP
  LParen : SystemP
  RParen : SystemP

build_sym : SystemP -> PR n
build_sym Zero = Const 1
build_sym F    = Const 3
build_sym Neg  = Const 5
build_sym Or   = Const 7
build_sym ForAll = Const 9
build_sym LParen = Const 11
build_sym RParen = Const 13

build_seq : SystemP -> PR n
build_seq sym = Comp seq [build_sym sym]

parens: PR 1
parens = Comp concat [build_seq LParen, Comp concat [Proj 1 0, Comp seq [build_seq RParen]]]

isVarType : PR 2                        --z        n         x
isVarType = Comp (exists bound cond) [Proj 2 1, Proj 2 0, Proj 2 1] where
  bound : PR 1
  cond  : PR 3
  bound = Proj 1 0
  cond  = Comp and [Comp lt [build_seq RParen, Proj 3 0],
                    Comp and [Comp isPrime [Proj 3 0], 
                              Comp equals [Comp exp [Proj 3 0, Proj 3 1], 
                                           Proj 3 2]]]

isVar : PR 1
isVar = Comp (exists bound cond) [Proj 1 0, Proj 1 0] where
  bound = Proj 1 0
  cond  = Comp isVarType [Proj 2 0, Proj 2 1]

-- FORMULA BUILDERS

form_not : PR 1
form_not = Comp concat [build_seq Neg, Comp parens [Proj 1 0]]

form_or : PR 2
form_or = Comp concat [Comp parens [Proj 2 0], Comp concat [build_seq ForAll, Comp parens [Proj 2 1]]]

form_forall : PR 2
form_forall = Comp concat [build_seq ForAll, Comp concat [Comp seq [Proj 2 0], Comp parens [Proj 2 1]]]

--- Expressions of type n

nthSucc : PR 2
nthSucc = Rec (Proj 1 0) (Comp concat [build_seq F, Proj 3 1])

num : Nat -> PR 0
num n = Comp nthSucc [Const n, build_seq Zero]

isType1 : PR 1                           --n        x
isType1 = Comp (exists bound1 cond1) [Proj 1 0, Proj 1 0] where
  bound1 = Proj 1 0                     --m          n       x
  cond1  = Comp (exists bound2 cond2) [Proj 2 1, Proj 2 0, Proj 2 1] where
    bound2 = Proj 1 0
    cond2  = Comp and [Comp equals [Proj 3 2, Comp nthSucc [Proj 3 1, Comp seq [Proj 3 0]]],
                       Comp or [Comp equals [Proj 3 0, build_seq Zero],
                                Comp isVarType [Const 1, Proj 3 0]]]

isTypeN : PR 2
isTypeN = Comp or [p1, p2] where
  p1 = Comp and [Comp equals [Proj 2 0, Const 1], Comp isType1 [Proj 2 1]]
  p2 = Comp and [Comp gt [Const 1, Proj 2 0], existential] where
    existential = Comp (exists (Proj 1 0) cond) [Proj 2 1, Proj 2 0, Proj 2 1] where
      cond = Comp and [Comp isVarType [Proj 3 1, Proj 3 0], Comp equals [Proj 3 2, Comp seq [Proj 3 0]]]

-- FORMULAS

isElForm : PR 1                           -- n        z         y         x
isElForm = Comp (exists (Proj 1 0) p1) [Proj 1 0, Proj 1 0, Proj 1 0, Proj 1 0] where
  p1 = Comp (exists (Proj 1 0) p2) [Proj 4 1, Proj 4 0, Proj 4 2, Proj 4 3] where -- z n y x
    p2 = Comp (exists (Proj 1 0) p3) [Proj 4 2, Proj 4 0, Proj 4 1, Proj 4 3]  where --y z n x
      p3 = Comp and [p4, Comp and [p5, p6]] where
        p4 = Comp isTypeN [Proj 4 2, Proj 4 0]
        p5 = Comp isTypeN [Comp Succ [Proj 4 2], Proj 4 1]
        p6 = Comp equals [Proj 4 1, Comp parens [Proj 4 0]]

isLogOp : PR 3
isLogOp = Comp or [is_not, Comp or [is_or, is_forall]] where
  is_not    = Comp equals [Proj 3 0, Comp form_not [Proj 3 1]]
  is_or     = Comp equals [Proj 3 0, Comp form_or [Proj 3 1, Proj 3 2]]
  is_forall = Comp (exists (Proj 1 0) is_equal) [Proj 3 0, Proj 3 0, Proj 3 1] where
    is_equal = Comp equals [Proj 3 1, Comp form_forall [Proj 3 0, Proj 3 2]]

isFormSeq : PR 1
isFormSeq = Comp and [Comp (forAll bound cond) [Proj 1 0, Proj 1 0], not_zero] where
  bound = Comp len [Proj 1 0]
  not_zero = Comp gt [Comp len [Proj 1 0], Const 0]
  cond  = Comp implies [Comp gt [Const 0, Proj 2 0], rhs] where
    rhs = Comp or [p1, ex1] where
      p1 = Comp isElForm [Comp mem [Proj 2 0, Proj 2 1]]
      ex1 = Comp (exists (Proj 1 0) ex2) [Proj 2 0, Proj 2 0, Proj 2 1] where -- q, n, x
        ex2 = Comp (exists (Proj 1 0) cond) [Proj 3 1, Proj 3 0, Proj 3 1, Proj 3 2] where -- p,q,n,x
          cond = Comp isLogOp [Comp mem [Proj 4 2, Proj 4 3],
                               Comp mem [Proj 4 0, Proj 4 3],
                               Comp mem [Proj 4 1, Proj 4 3]]
