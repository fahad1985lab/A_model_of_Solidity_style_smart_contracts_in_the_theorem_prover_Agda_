module libraries.natCompare  where


open import Data.Nat  hiding (_≤_ ; _<_ )
open import Data.Bool hiding (_≤_ ; _<_)
open import Data.Empty
open import Data.Unit


atom : Bool → Set
atom true = ⊤
atom false = ⊥

_≦b_ : ℕ → ℕ → Bool
0 ≦b m = true
suc n ≦b zero = false
suc n ≦b suc m = n ≦b m

_==b_ : ℕ → ℕ → Bool
0 ==b 0  = true
0 ==b suc n  = false
suc n ==b 0 = false
suc n ==b suc m = n ==b m

-- ≦r  is a recursively defined ≦
_≦r_ : ℕ → ℕ → Set
n ≦r m = atom (n ≦b m)


_==r_ : ℕ → ℕ → Set
n ==r m = atom (n ==b m)

_<r_ : ℕ → ℕ → Set
n <r m = suc n ≦r m

0≦n : {n : ℕ} → 0 ≦r n
0≦n = tt

data OrderingLeq (n m :  ℕ) : Set where
   leq     : n ≦r m → OrderingLeq n m
   greater : m <r  n  → OrderingLeq n m


liftLeq : {n m : ℕ} → OrderingLeq n m → OrderingLeq (suc n) (suc m)
liftLeq {n} {m} (leq x) = leq x
liftLeq {n} {m} (greater x) = greater x


compareLeq : (n m : ℕ) → OrderingLeq n m
compareLeq zero n = leq tt
compareLeq (suc n) zero = greater tt
compareLeq (suc n) (suc m) = liftLeq (compareLeq n m)


data OrderingLess (n m :  ℕ) : Set where
   less     : n <r m → OrderingLess n m
   geq      : m ≦r  n  → OrderingLess n m


liftLess : {n m : ℕ} → OrderingLess n m → OrderingLess (suc n) (suc m)
liftLess {n} {m} (less x) = less x
liftLess {n} {m} (geq x) = geq x


compareLess : (n m : ℕ) → OrderingLess n m
compareLess n zero = geq tt
compareLess zero (suc m) = less tt
compareLess (suc n) (suc m) = liftLess (compareLess n m)



subtract : (n m : ℕ) → m ≦r n → ℕ
subtract n zero nm = n
subtract (suc n) (suc m) nm = subtract n m nm
