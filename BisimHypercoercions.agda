module BisimHypercoercions
  (Label : Set)
  where
open import Types

module R where
  open import ReversibleHypercoercions Label public

module N where
  open import Hypercoercions Label public

mutual
  record CastSim (S T : Type) : Set where
    inductive
    field
      c1 : R.Cast S T
      c2 : N.Cast S T
      prf : Sim' c1 c2

  data CastSim' : ∀ {S T} → R.Cast S T → N.Cast S T → Set where

    mk-cast : ∀ {S T l}
      → Sim' (R.mk-cast S l T)
             (N.mk-cast S l T)
              
    mk-id : ∀ {T}
        → Sim' (R.mk-id T)
               (N.mk-id T)

    mk-seq : ∀ {R S T}
      → (s1 : Sim R S)
      → (s2 : Sim S T)
      → Sim' (R.mk-seq (Sim.c1 s1) (Sim.c1 s2))
             (N.mk-seq (Sim.c2 s1) (Sim.c2 s2))

