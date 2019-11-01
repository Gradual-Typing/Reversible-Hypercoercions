module Hypercoercions (Label : Set) where

open import Types
open import Variables
open import Terms Label
open import CastADT Label

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)

data Head : PreType → Type → Set where
  ⁇ : ∀ {P} →
    (l : Label) →
    ---
    Head P ⋆
  ε : ∀ {P} →
    ---
    Head P (` P)

data Tail : PreType → Type → Set where
  ‼ : ∀ {P} →
    ---
    Tail P ⋆
  ε : ∀ {P} →
    ---
    Tail P (` P)

mutual
  data Cast : Type → Type → Set where
    id⋆ :
      ---
      Cast ⋆ ⋆
    ↷ : ∀ {A P Q B} →
      (t1 : Head P A) →
      (m  : Mid P Q) →
      (t2 : Tail Q B) →
      ---
      Cast A B
    
  data Mid : PreType → PreType → Set where
    ⊥_ : ∀ {P Q} → 
      (l : Label) →
      ---
      Mid P Q
    `_ : ∀ {P Q} →
      (m : PreMid P Q) →
      ---
      Mid P Q

  data PreMid : PreType → PreType → Set where
    U :
      ---
      PreMid U U
    _⇒_ : ∀ {S1 S2 T1 T2} →
      (c₁ : Cast S2 S1) →
      (c₂ : Cast T1 T2) →
      ---
      PreMid (S1 ⇒ T1) (S2 ⇒ T2)
    _⊗_ : ∀ {S1 S2 T1 T2} →
      (c₁ : Cast S1 S2) →
      (c₂ : Cast T1 T2) →
      ---
      PreMid (S1 ⊗ T1) (S2 ⊗ T2)
    _⊕_ : ∀ {S1 S2 T1 T2} →
      (c₁ : Cast S1 S2) →
      (c₂ : Cast T1 T2) →
      ---
      PreMid (S1 ⊕ T1) (S2 ⊕ T2)
    ref : ∀ {S T} →
      (c : Cast S T) →
      ---
      PreMid (ref S) (ref T)
    
GapP : PreType → PreType → Set
GapP P1 P2 = P1 ≡ P2 ⊎ Label

GapT : Type → Type → Set
GapT T1 T2 = T1 ≡ T2 ⊎ Label

ℓ-dom : ∀ {T1 T2 T3 T4}
  → GapP (T1 ⇒ T2) (T3 ⇒ T4)
  → GapT T3 T1
ℓ-dom (inj₁ refl) = inj₁ refl
ℓ-dom (inj₂ l1) = inj₂ l1

ℓ-cod : ∀ {T1 T2 T3 T4}
  → GapP (T1 ⇒ T2) (T3 ⇒ T4)
  → GapT T2 T4
ℓ-cod (inj₁ refl) = inj₁ refl
ℓ-cod (inj₂ l) = inj₂ l

ℓ-car : ∀ {T1 T2 T3 T4}
  → GapP (T1 ⊗ T2) (T3 ⊗ T4)
  → GapT T1 T3
ℓ-car (inj₁ refl) = inj₁ refl
ℓ-car (inj₂ l) = inj₂ l

ℓ-cdr : ∀ {T1 T2 T3 T4}
  → GapP (T1 ⊗ T2) (T3 ⊗ T4)
  → GapT T2 T4
ℓ-cdr (inj₁ refl) = inj₁ refl
ℓ-cdr (inj₂ l) = inj₂ l

ℓ-inl : ∀ {T1 T2 T3 T4}
  → GapP (T1 ⊕ T2) (T3 ⊕ T4)
  → GapT T1 T3
ℓ-inl (inj₁ refl) = inj₁ refl
ℓ-inl (inj₂ l) = inj₂ l

ℓ-inr : ∀ {T1 T2 T3 T4}
  → GapP (T1 ⊕ T2) (T3 ⊕ T4)
  → GapT T2 T4
ℓ-inr (inj₁ refl) = inj₁ refl
ℓ-inr (inj₂ l) = inj₂ l

ℓ-ref : ∀ {S T} →
  GapP (ref S) (ref T) →
  ---
  GapT S T
ℓ-ref (inj₁ refl) = inj₁ refl
ℓ-ref (inj₂ ll) = (inj₂ ll)

mk-head : ∀ {T P}
  → Head  P T
  → GapT ⋆ T
  ---
  → Head P ⋆
mk-head (⁇ l) g = (⁇ l)
mk-head ε (inj₁ ())
mk-head ε (inj₂ l1) = ⁇ l1

mk-tail : ∀ {T P}
  → Tail  P T
  → GapT T ⋆
  ---
  → Tail P ⋆
mk-tail ‼ g = ‼
mk-tail ε (inj₁ ())
mk-tail ε (inj₂ l) = ‼

mutual
  seq : ∀ {T1 T2 T3 T4}
    → Cast T1 T2
    → GapT T2 T3
    → Cast T3 T4
  ----------------
    → Cast T1 T4
  seq id⋆ g id⋆ = id⋆
  seq id⋆ g (↷ t1 m t2) = ↷ (mk-head t1 g) m t2
  seq (↷ t1 m t2) g id⋆ = ↷ t1 m (mk-tail t2 g)
  seq (↷ t1 m1 t2) g (↷ t3 m2 t4) = ↷ t1 (seq-m m1 (link t2 g t3) m2) t4
  
  seq-m : ∀ {P1 P2 P3 P4}
    → Mid P1 P2
    → GapP P2 P3
    → Mid P3 P4
    ---
    → Mid P1 P4
  seq-m {P2 = P2} {P3 = P3} m1 g m2 with (` P2) ⌣? (` P3)
  seq-m (⊥ l1) g (⊥ l2) | yes p = ⊥ l1
  seq-m (⊥ l) g (` m) | yes p = ⊥ l
  seq-m (` m) g (⊥ l) | yes p = ⊥ l
  seq-m (` m1) g (` m2) | yes p = ` seq-mm p m1 g m2
  seq-m m1 g m2 | no ¬p with g
  seq-m m1 g m2 | no ¬p | inj₁ refl = ⊥-elim (¬p (⌣refl _))
  seq-m m1 g m2 | no ¬p | inj₂ l = ⊥ l

  seq-mm : ∀ {P1 P2 P3 P4}
    → (` P2) ⌣ (` P3)
    → PreMid P1 P2
    → GapP P2 P3
    → PreMid P3 P4
    ---
    → PreMid P1 P4
  seq-mm ⌣U U g U = U
  seq-mm ⌣⇒ (c₁ ⇒ c₂) g (c₃ ⇒ c₄) = (seq c₃ (ℓ-dom g) c₁) ⇒ (seq c₂ (ℓ-cod g) c₄)
  seq-mm ⌣⊗ (c₁ ⊗ c₂) g (c₃ ⊗ c₄) = (seq c₁ (ℓ-car g) c₃) ⊗ (seq c₂ (ℓ-cdr g) c₄)
  seq-mm ⌣⊕ (c₁ ⊕ c₂) g (c₃ ⊕ c₄) = (seq c₁ (ℓ-inl g) c₃) ⊕ (seq c₂ (ℓ-inr g) c₄)
  seq-mm ⌣! (ref c1) g (ref c2) = ref (seq c1 (ℓ-ref g) c2)

  link : ∀ {P S T Q}
    → Tail P S
    → GapT S T
    → Head Q T
    -----------------
    → GapP P Q
  link ‼ (inj₁ refl) (⁇ l) = inj₂ l
  link ‼ (inj₂ ll) (⁇ l2) = inj₂ l2
  link ‼ (inj₂ l1) ε = inj₂ l1
  link ε (inj₁ refl) ε = inj₁ refl
  link ε (inj₂ l1) (⁇ l) = inj₂ l
  link ε (inj₂ ll) ε = inj₂ ll

mutual
  mk-id : ∀ T → Cast T T
  mk-id ⋆
    = id⋆
  mk-id (` P)
    = ↷ ε (` mk-mid P) ε

  mk-mid : ∀ P → PreMid P P
  mk-mid U
    = U
  mk-mid (T₁ ⇒ T₂)
    = mk-id T₁ ⇒ mk-id T₂
  mk-mid (T₁ ⊗ T₂)
    = mk-id T₁ ⊗ mk-id T₂
  mk-mid (T₁ ⊕ T₂)
    = mk-id T₁ ⊕ mk-id T₂
  mk-mid (ref T)
    = ref (mk-id T)

mk-cast : Label → ∀ T1 T2 → Cast T1 T2
mk-cast l T1 T2 = seq (mk-id T1) (inj₂ l) (mk-id T2)

mk-seq : ∀ {T1 T2 T3} → Cast T1 T2 → Cast T2 T3 → Cast T1 T3
mk-seq c1 c2 = seq c1 (inj₁ refl) c2

mutual
  seq-id-l : ∀ {T1 T2} → (c : Cast T1 T2) → mk-seq (mk-id T1) c ≡ c
  seq-id-l id⋆ = refl
  seq-id-l (↷ (⁇ l) m t2) = refl
  seq-id-l {T1 = ` P} (↷ ε (⊥ l) t2) with P
  seq-id-l {` P} (↷ ε (⊥ l) t2) | U = refl
  seq-id-l {` P} (↷ ε (⊥ l) t2) | T₁ ⇒ T₂ = refl
  seq-id-l {` P} (↷ ε (⊥ l) t2) | T₁ ⊗ T₂ = refl
  seq-id-l {` P} (↷ ε (⊥ l) t2) | T₁ ⊕ T₂ = refl
  seq-id-l {` P} (↷ ε (⊥ l) t2) | ref T₁ = refl
  seq-id-l (↷ ε (` U) t2) = refl
  seq-id-l (↷ ε (` (c₁ ⇒ c₂)) t2) rewrite seq-id-r c₁ | seq-id-l c₂ = refl
  seq-id-l (↷ ε (` (c₁ ⊗ c₂)) t2) rewrite seq-id-l c₁ | seq-id-l c₂ = refl
  seq-id-l (↷ ε (` (c₁ ⊕ c₂)) t2) rewrite seq-id-l c₁ | seq-id-l c₂ = refl
  seq-id-l (↷ ε (` ref c) t2) rewrite seq-id-l c = refl
  
  seq-id-r : ∀ {T1 T2} → (c : Cast T1 T2) → mk-seq c (mk-id T2) ≡ c
  seq-id-r id⋆ = refl
  seq-id-r (↷ t1 m ‼) = refl
  seq-id-r {T2 = ` P} (↷ t1 (⊥ l) ε) with P
  seq-id-r (↷ t1 (⊥ l) ε) | U = refl
  seq-id-r (↷ t1 (⊥ l) ε) | T₁ ⇒ T₂ = refl
  seq-id-r (↷ t1 (⊥ l) ε) | T₁ ⊗ T₂ = refl
  seq-id-r (↷ t1 (⊥ l) ε) | T₁ ⊕ T₂ = refl
  seq-id-r (↷ t1 (⊥ l) ε) | ref T₁ = refl
  seq-id-r (↷ t1 (` U) ε) = refl
  seq-id-r (↷ t1 (` (c₁ ⇒ c₂)) ε) rewrite seq-id-l c₁ | seq-id-r c₂ = refl
  seq-id-r (↷ t1 (` (c₁ ⊗ c₂)) ε) rewrite seq-id-r c₁ | seq-id-r c₂ = refl
  seq-id-r (↷ t1 (` (c₁ ⊕ c₂)) ε) rewrite seq-id-r c₁ | seq-id-r c₂ = refl
  seq-id-r (↷ t1 (` ref c) ε)  rewrite seq-id-r c = refl

open import Values Label Cast

blame-gap : {P1 P2 : PreType}
  → GapP P1 P2
  → ¬ ((` P1) ⌣ (` P2))
  ---
  → Label
blame-gap (inj₁ refl) ¬p = ⊥-elim (¬p (⌣refl _))
blame-gap (inj₂ l) ¬p = l

mutual
  apply-cast : ∀ {T1 T2}
    → Cast T1 T2
    → Val T1
    ---
    → CastResult T2
  apply-cast id⋆ v = succ v
  apply-cast (↷ (⁇ l) m t2) (dyn v) = apply-rest (inj₂ l) m t2 v
  apply-cast (↷ ε m t2) v = apply-rest (inj₁ refl) m t2 v

  apply-rest : ∀ {P1 P2 P3 T}
    → GapP P1 P2
    → Mid P2 P3
    → Tail P3 T
    → Val (` P1)
    ---
    → CastResult T
  apply-rest g m t v with apply-mid g m v
  apply-rest g m t v | succ u = succ (apply-tail t u)
  apply-rest g m t v | fail l = fail l

  apply-tail : ∀ {P T} → Tail P T → Val (` P) → Val T
  apply-tail ‼ v = dyn v
  apply-tail ε v = v

  apply-mid : ∀ {P1 P2 P3}
    → GapP P1 P2
    → Mid P2 P3
    → Val (` P1)
    ---
    → CastResult (` P3)
  apply-mid {P1} {P2} g m v with (` P1) ⌣? (` P2)
  apply-mid g m v | yes p with m
  apply-mid g m v | yes p | ⊥ l1 = fail l1
  apply-mid g m v | yes p | ` mm = succ (apply-premid g p mm v)
  apply-mid {P1} {P2} g m v | no ¬p = fail (blame-gap g ¬p)

  apply-premid : ∀ {P1 P2 P3}
    → GapP P1 P2
    → (` P1) ⌣ (` P2)
    → PreMid P2 P3
    → Val (` P1)
    ---
    → Val (` P3)
  apply-premid g ⌣U U sole = sole
  apply-premid g ⌣⇒ (d1 ⇒ d2) (fun env c1 e c2)
    = fun env (seq d1 (ℓ-dom g) c1) e (seq c2 (ℓ-cod g) d2)
  apply-premid g ⌣⊗ (d1 ⊗ d2) (cons v1 c1 v2 c2)
    = cons v1 (seq c1 (ℓ-car g) d1) v2 (seq c2 (ℓ-cdr g) d2)
  apply-premid g ⌣⊕ (d1 ⊕ d2) (inl v c)
    = inl v (seq c (ℓ-inl g) d1) 
  apply-premid g ⌣⊕ (d1 ⊕ d2) (inr v c)
    = inr v (seq c (ℓ-inr g) d2) 
  apply-premid g ⌣! (ref d) (box v c)
    = box v (seq c (ℓ-ref g) d)
