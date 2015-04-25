module Data.BoundedLIFO where

open import Data.List hiding (take)
import      Data.List as L
open import Data.Nat

data BoundedLIFO {l} (A : Set l) : ℕ → Set l where
  bl : (n : ℕ) → (l : List A) → (length l ≤ n) → BoundedLIFO A n

toList : ∀ {l} {A : Set l} {n : ℕ} → BoundedLIFO A n → List A
toList (bl _ l _) = l

empty : ∀ {l} {A : Set l} → (n : ℕ) → BoundedLIFO A n
empty n = bl n [] z≤n

put : ∀ {l} {A : Set l} → {n : ℕ} → List A → BoundedLIFO A n → BoundedLIFO A n
put l (bl n l' _) = bl n (L.take n lsum) (length﹍take﹍n﹍≤﹍n n lsum)
  where
  lsum = l ++ l'

  length﹍take﹍n﹍≤﹍n : ∀ {A} (n : ℕ) (l : List A) → length (L.take n l) ≤ n
  length﹍take﹍n﹍≤﹍n zero _ = z≤n
  length﹍take﹍n﹍≤﹍n (suc n) [] = z≤n
  length﹍take﹍n﹍≤﹍n (suc n) (x ∷ xs) = s≤s (length﹍take﹍n﹍≤﹍n n xs)

put_into_ : ∀ {l} {A : Set l} {n m : ℕ} → BoundedLIFO A n → BoundedLIFO A m → BoundedLIFO A m
put a into b = put (toList a) b

take : ∀ {l} {A : Set l} → {n : ℕ} → (k : ℕ) → BoundedLIFO A n → List A
take k (bl _ l _) = L.take k l
