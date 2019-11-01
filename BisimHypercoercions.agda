module BisimHypercoercions
  (Label : Set)
  where
open import Types

module R where
  open import ReversibleHypercoercions Label public

module N where
  open import Hypercoercions Label public

mutual
  data Sim' : ∀ {S T} → R.Cast S T → N.Cast S T → Set where

    mk-cast : ∀ {S T l}
      → Sim' (R.mk-cast S l T)
             (N.mk-cast S l T)
              
    mk-id : ∀ {T}
        → Sim' (R.mk-id T)
               (N.mk-id T)

  record Sim (S T : Type) : Set where
    field
      c1 : R.Cast S T
      c2 : N.Cast S T
