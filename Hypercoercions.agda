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

data Tip : PreType → Type → Set where
  ⁇ : ∀ {P} →
    (l : Label) →
    ---
    Tip P ⋆
  ε : ∀ {P} →
    ---
    Tip P (` P)

mutual
  data Cast : Type → Type → Set where
    id⋆ :
      ---
      Cast ⋆ ⋆
    ↷ : ∀ {A P Q B} →
      (t1 : Tip P A) →
      (m  : Mid P Q) →
      (t2 : Tip Q B) →
      ---
      Cast A B
    
  data Mid : PreType → PreType → Set where
    _⊥_ : ∀ {P Q} → 
      (l1 l2 : Label) →
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
GapP P1 P2 = P1 ≡ P2 ⊎ (Label × Label)

rev-GapP : ∀ {P Q} →
  GapP P Q →
  ---
  GapP Q P
rev-GapP (inj₁ refl) = inj₁ refl
rev-GapP (inj₂ (l1 , l2)) = inj₂ (l2 , l1)

GapT : Type → Type → Set
GapT T1 T2 = T1 ≡ T2 ⊎ (Label × Label)

rev-GapT : ∀ {P Q} →
  GapT P Q →
  ---
  GapT Q P
rev-GapT (inj₁ refl) = inj₁ refl
rev-GapT (inj₂ (l1 , l2)) = inj₂ (l2 , l1)

ℓ-dom : ∀ {T1 T2 T3 T4}
  → GapP (T1 ⇒ T2) (T3 ⇒ T4)
  → GapT T3 T1
ℓ-dom (inj₁ refl) = inj₁ refl
ℓ-dom (inj₂ (l1 , l2)) = inj₂ (l2 , l1)

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

mk-tipl : ∀ {T P}
  → Tip  P T
  → GapT ⋆ T
  ---(inj₂ y)
  → Tip P ⋆
mk-tipl (⁇ l) g = (⁇ l)
mk-tipl ε (inj₁ ())
mk-tipl ε (inj₂ (l1 , l2)) = ⁇ l1

mk-tipr : ∀ {T P}
  → Tip  P T
  → GapT T ⋆
  ---
  → Tip P ⋆
mk-tipr (⁇ l) g = (⁇ l)
mk-tipr ε (inj₁ ())
mk-tipr ε (inj₂ (l1 , l2)) = ⁇ l2

mutual
  seq : ∀ {T1 T2 T3 T4}
    → Cast T1 T2
    → GapT T2 T3
    → Cast T3 T4
  ----------------
    → Cast T1 T4
  seq id⋆ g id⋆ = id⋆
  seq id⋆ g (↷ t1 m t2) = ↷ (mk-tipl t1 g) m t2
  seq (↷ t1 m t2) g id⋆ = ↷ t1 m (mk-tipr t2 g)
  seq (↷ t1 m1 t2) g (↷ t3 m2 t4) = ↷ t1 (seq-m m1 (link t2 g t3) m2) t4
  
  seq-m : ∀ {P1 P2 P3 P4}
    → Mid P1 P2
    → GapP P2 P3
    → Mid P3 P4
    ---
    → Mid P1 P4
  seq-m {P2 = P2} {P3 = P3} m1 g m2 with (` P2) ⌣? (` P3)
  seq-m (l1 ⊥ l2) g (l3 ⊥ l4) | yes p = l1 ⊥ l4
  seq-m (l1 ⊥ l2) g (` m) | yes p = l1 ⊥ l2
  seq-m (` m) g (l1 ⊥ l2) | yes p = l1 ⊥ l2
  seq-m (` m1) g (` m2) | yes p = ` seq-mm p m1 g m2
  seq-m m1 g m2 | no ¬p with g
  seq-m m1 g m2 | no ¬p | inj₁ refl = ⊥-elim (¬p (⌣refl _))
  seq-m m1 g m2 | no ¬p | inj₂ (l1 , l2) = l1 ⊥ l2

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
    → Tip P S
    → GapT S T
    → Tip Q T
    -----------------
    → GapP P Q
  link (⁇ l1) (inj₁ refl) (⁇ l2) = inj₂ (l2 , l1)
  link (⁇ l1) (inj₂ ll) (⁇ l2) = inj₂ (l2 , l1)
  link (⁇ l) (inj₂ (l1 , l2)) ε = inj₂ (l1 , l)
  link ε (inj₁ refl) ε = inj₁ refl
  link ε (inj₂ (l1 , l2)) (⁇ l) = inj₂ (l , l2)
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
mk-cast l T1 T2 = seq (mk-id T1) (inj₂ (l , l)) (mk-id T2)

mutual
  mk-rev-premid : ∀ {S T} →
    PreMid S T →
    ---
    PreMid T S
  mk-rev-premid U = U
  mk-rev-premid (c₁ ⇒ c₂) = (mk-rev c₁) ⇒ (mk-rev c₂)
  mk-rev-premid (c₁ ⊗ c₂) = (mk-rev c₁) ⊗ (mk-rev c₂)
  mk-rev-premid (c₁ ⊕ c₂) = (mk-rev c₁) ⊕ (mk-rev c₂)
  mk-rev-premid (ref c) = ref (mk-rev c)
    
  mk-rev-mid : ∀ {S T} →
    Mid S T →
    ---
    Mid T S
  mk-rev-mid (l1 ⊥ l2) = l2 ⊥ l1
  mk-rev-mid (` m) = ` mk-rev-premid m

  mk-rev : ∀ {S T} →
    Cast S T →
    ---
    Cast T S
  mk-rev id⋆ = id⋆
  mk-rev (↷ t1 m t2) = (↷ t2 (mk-rev-mid m) t1)

mk-seq : ∀ {T1 T2 T3} → Cast T1 T2 → Cast T2 T3 → Cast T1 T3
mk-seq c1 c2 = seq c1 (inj₁ refl) c2

mutual
  seq-id-l : ∀ {T1 T2} → (c : Cast T1 T2) → mk-seq (mk-id T1) c ≡ c
  seq-id-l id⋆ = refl
  seq-id-l (↷ (⁇ l) m t2) = refl
  seq-id-l {T1 = ` P} (↷ ε (l1 ⊥ l2) t2) with P
  seq-id-l {` P} (↷ ε (l1 ⊥ l2) t2) | U = refl
  seq-id-l {` P} (↷ ε (l1 ⊥ l2) t2) | T₁ ⇒ T₂ = refl
  seq-id-l {` P} (↷ ε (l1 ⊥ l2) t2) | T₁ ⊗ T₂ = refl
  seq-id-l {` P} (↷ ε (l1 ⊥ l2) t2) | T₁ ⊕ T₂ = refl
  seq-id-l {` P} (↷ ε (l1 ⊥ l2) t2) | ref T₁ = refl
  seq-id-l (↷ ε (` U) t2) = refl
  seq-id-l (↷ ε (` (c₁ ⇒ c₂)) t2) rewrite seq-id-r c₁ | seq-id-l c₂ = refl
  seq-id-l (↷ ε (` (c₁ ⊗ c₂)) t2) rewrite seq-id-l c₁ | seq-id-l c₂ = refl
  seq-id-l (↷ ε (` (c₁ ⊕ c₂)) t2) rewrite seq-id-l c₁ | seq-id-l c₂ = refl
  seq-id-l (↷ ε (` ref c) t2) rewrite seq-id-l c = refl
  
  seq-id-r : ∀ {T1 T2} → (c : Cast T1 T2) → mk-seq c (mk-id T2) ≡ c
  seq-id-r id⋆ = refl
  seq-id-r (↷ t1 m (⁇ l)) = refl
  seq-id-r {T2 = ` P} (↷ t1 (l1 ⊥ l2) ε) with P
  seq-id-r (↷ t1 (l1 ⊥ l2) ε) | U = refl
  seq-id-r (↷ t1 (l1 ⊥ l2) ε) | T₁ ⇒ T₂ = refl
  seq-id-r (↷ t1 (l1 ⊥ l2) ε) | T₁ ⊗ T₂ = refl
  seq-id-r (↷ t1 (l1 ⊥ l2) ε) | T₁ ⊕ T₂ = refl
  seq-id-r (↷ t1 (l1 ⊥ l2) ε) | ref T₁ = refl
  seq-id-r (↷ t1 (` U) ε) = refl
  seq-id-r (↷ t1 (` (c₁ ⇒ c₂)) ε) rewrite seq-id-l c₁ | seq-id-r c₂ = refl
  seq-id-r (↷ t1 (` (c₁ ⊗ c₂)) ε) rewrite seq-id-r c₁ | seq-id-r c₂ = refl
  seq-id-r (↷ t1 (` (c₁ ⊕ c₂)) ε) rewrite seq-id-r c₁ | seq-id-r c₂ = refl
  seq-id-r (↷ t1 (` ref c) ε)  rewrite seq-id-r c = refl

lem-rev-idem : ∀ {S T} →
  (c : Cast S T) →
  ---
  mk-rev (mk-rev c) ≡ c
lem-rev-idem id⋆ = refl
lem-rev-idem (↷ t1 (l1 ⊥ l2) t2) = refl
lem-rev-idem (↷ t1 (` U) t2) = refl
lem-rev-idem (↷ t1 (` (c₁ ⇒ c₂)) t2)
  rewrite lem-rev-idem c₁ | lem-rev-idem c₂
  = refl
lem-rev-idem (↷ t1 (` (c₁ ⊗ c₂)) t2)
  rewrite lem-rev-idem c₁ | lem-rev-idem c₂
  = refl
lem-rev-idem (↷ t1 (` (c₁ ⊕ c₂)) t2)
  rewrite lem-rev-idem c₁ | lem-rev-idem c₂
  = refl
lem-rev-idem (↷ t1 (` ref c) t2)
  rewrite lem-rev-idem c
  = refl

lem-tipr-rev : ∀ {T P} →
  (t : Tip P T) →
  (g : GapT ⋆ T) →
  (mk-tipr t (rev-GapT g)) ≡ (mk-tipl t g)
lem-tipr-rev (⁇ l) g = refl
lem-tipr-rev ε (inj₁ ())
lem-tipr-rev ε (inj₂ y) = refl

lem-tipl-rev : ∀ {T P} →
  (t : Tip P T) →
  (g : GapT T ⋆) →
  (mk-tipl t (rev-GapT g)) ≡ (mk-tipr t g)
lem-tipl-rev (⁇ l) g = refl
lem-tipl-rev ε (inj₁ ())
lem-tipl-rev ε (inj₂ y) = refl

lem-link-rev : ∀ {S T P Q} →
  (t1 : Tip Q S)
  (g  : GapT S T)
  (t2 : Tip P T) →
  ---
  link t2 (rev-GapT g) t1 ≡ rev-GapP (link t1 g t2)
lem-link-rev (⁇ l) (inj₁ refl) (⁇ l₁) = refl
lem-link-rev (⁇ l) (inj₂ y) (⁇ l₁) = refl
lem-link-rev (⁇ l) (inj₂ y) ε = refl
lem-link-rev ε (inj₁ refl) ε = refl
lem-link-rev ε (inj₂ y) (⁇ l) = refl
lem-link-rev ε (inj₂ y) ε = refl

ℓ-dom-rev : ∀ {T1 T2 T3 T4}
  → (g : GapP (T1 ⇒ T2) (T3 ⇒ T4))
  ---
  → ℓ-dom (rev-GapP g) ≡ rev-GapT (ℓ-dom g)
ℓ-dom-rev (inj₁ refl) = refl
ℓ-dom-rev (inj₂ y) = refl

ℓ-cod-rev : ∀ {T1 T2 T3 T4}
  → (g : GapP (T1 ⇒ T2) (T3 ⇒ T4))
  ---
  → ℓ-cod (rev-GapP g) ≡ rev-GapT (ℓ-cod g)
ℓ-cod-rev (inj₁ refl) = refl
ℓ-cod-rev (inj₂ y) = refl

ℓ-car-rev : ∀ {T1 T2 T3 T4}
  → (g : GapP (T1 ⊗ T2) (T3 ⊗ T4))
  ---
  → ℓ-car (rev-GapP g) ≡ rev-GapT (ℓ-car g)
ℓ-car-rev (inj₁ refl) = refl
ℓ-car-rev (inj₂ y) = refl

ℓ-cdr-rev : ∀ {T1 T2 T3 T4}
  → (g : GapP (T1 ⊗ T2) (T3 ⊗ T4))
  ---
  → ℓ-cdr (rev-GapP g) ≡ rev-GapT (ℓ-cdr g)
ℓ-cdr-rev (inj₁ refl) = refl
ℓ-cdr-rev (inj₂ y) = refl

ℓ-inl-rev : ∀ {T1 T2 T3 T4}
  → (g : GapP (T1 ⊕ T2) (T3 ⊕ T4))
  ---
  → ℓ-inl (rev-GapP g) ≡ rev-GapT (ℓ-inl g)
ℓ-inl-rev (inj₁ refl) = refl
ℓ-inl-rev (inj₂ y) = refl

ℓ-inr-rev : ∀ {T1 T2 T3 T4}
  → (g : GapP (T1 ⊕ T2) (T3 ⊕ T4))
  ---
  → ℓ-inr (rev-GapP g) ≡ rev-GapT (ℓ-inr g)
ℓ-inr-rev (inj₁ refl) = refl
ℓ-inr-rev (inj₂ y) = refl

ℓ-ref-rev : ∀ {T1 T3}
  → (g : GapP (ref T1) (ref T3))
  ---
  → ℓ-ref (rev-GapP g) ≡ rev-GapT (ℓ-ref g)
ℓ-ref-rev (inj₁ refl) = refl
ℓ-ref-rev (inj₂ y) = refl

lem-seq-rev : ∀ {T1 T2 T3 T4}
  → (c1 : Cast T1 T2)
  → (g  : GapT T2 T3)
  → (c2 : Cast T3 T4)
  ---
  → mk-rev (seq (mk-rev c2) (rev-GapT g) (mk-rev c1)) ≡ seq c1 g c2
lem-seq-rev id⋆ g id⋆ = refl
lem-seq-rev id⋆ g (↷ t1 m t2)
  rewrite lem-tipr-rev t1 g
  = lem-rev-idem (↷ (mk-tipl t1 g) m t2)
lem-seq-rev (↷ t1 m t2) g id⋆
  rewrite lem-tipl-rev t2 g
  = lem-rev-idem (↷ t1 m (mk-tipr t2 g))
lem-seq-rev (↷ {Q = Q} t1 m1 t2) g (↷ {P = P} t3 m2 t4) with (` Q) ⌣? (` P) | (` P) ⌣? (` Q)
lem-seq-rev (↷ {Q = Q} t1 (l1 ⊥ l2) t2) g (↷ {P = P} t3 (l3 ⊥ l4) t4) | yes p1 | yes p2 = refl
lem-seq-rev (↷ {Q = Q} t1 (l1 ⊥ l2) t2) g (↷ {P = P} t3 (` m) t4) | yes p1 | yes p2 = refl
lem-seq-rev (↷ {Q = Q} t1 (` m) t2) g (↷ {P = P} t3 (l1 ⊥ l2) t4) | yes p1 | yes p2 = refl
lem-seq-rev (↷ {Q = .U} t1 (` U) t2) g (↷ {P = .U} t3 (` U) t4) | yes ⌣U | yes ⌣U = refl
lem-seq-rev (↷ {Q = .(_ ⇒ _)} t1 (` (c₁ ⇒ c₂)) t2) g (↷ {P = .(_ ⇒ _)} t3 (` (c₃ ⇒ c₄)) t4) | yes ⌣⇒ | yes ⌣⇒
  rewrite lem-link-rev t2 g t3
  | ℓ-dom-rev (link t2 g t3) | lem-seq-rev c₃ (ℓ-dom (link t2 g t3)) c₁
  | ℓ-cod-rev (link t2 g t3) | lem-seq-rev c₂ (ℓ-cod (link t2 g t3)) c₄
  = refl
lem-seq-rev (↷ {Q = .(_ ⊗ _)} t1 (` (c₁ ⊗ c₂)) t2) g (↷ {P = .(_ ⊗ _)} t3 (` (c₃ ⊗ c₄)) t4) | yes ⌣⊗ | yes ⌣⊗
  rewrite lem-link-rev t2 g t3
  | ℓ-car-rev (link t2 g t3) | lem-seq-rev c₁ (ℓ-car (link t2 g t3)) c₃
  | ℓ-cdr-rev (link t2 g t3) | lem-seq-rev c₂ (ℓ-cdr (link t2 g t3)) c₄
  = refl
lem-seq-rev (↷ {Q = .(_ ⊕ _)} t1 (` (c₁ ⊕ c₂)) t2) g (↷ {P = .(_ ⊕ _)} t3 (` (c₃ ⊕ c₄)) t4) | yes ⌣⊕ | yes ⌣⊕
  rewrite lem-link-rev t2 g t3
  | ℓ-inl-rev (link t2 g t3) | lem-seq-rev c₁ (ℓ-inl (link t2 g t3)) c₃
  | ℓ-inr-rev (link t2 g t3) | lem-seq-rev c₂ (ℓ-inr (link t2 g t3)) c₄
  = refl
lem-seq-rev (↷ {Q = .(ref _)} t1 (` ref c₁) t2) g (↷ {P = .(ref _)} t3 (` ref c₃) t4) | yes ⌣! | yes ⌣!
  rewrite lem-link-rev t2 g t3
  | ℓ-ref-rev (link t2 g t3) | lem-seq-rev c₁ (ℓ-ref (link t2 g t3)) c₃
  = refl
lem-seq-rev (↷ {Q = Q} t1 m1 t2) g (↷ {P = P} t3 m2 t4) | yes p1 | no ¬p2 = ⊥-elim (¬p2 (⌣symm p1))
lem-seq-rev (↷ {Q = Q} t1 m1 t2) g (↷ {P = P} t3 m2 t4) | no ¬p1 | yes p2 = ⊥-elim (¬p1 (⌣symm p2))
lem-seq-rev (↷ {Q = Q} t1 m1 t2) g (↷ {P = P} t3 m2 t4) | no ¬p1 | no ¬p2
  rewrite lem-link-rev t2 g t3
  with link t2 g t3
... | inj₁ refl = (⊥-elim (¬p1 (⌣refl (` Q))))
... | inj₂ y = refl

open import Values Label Cast

blame-gap : {P1 P2 : PreType}
  → GapP P1 P2
  → ¬ ((` P1) ⌣ (` P2))
  ---
  → Label
blame-gap (inj₁ refl) ¬p = ⊥-elim (¬p (⌣refl _))
blame-gap (inj₂ (l , _)) ¬p = l

mutual
  apply-cast : ∀ {T1 T2}
    → Cast T1 T2
    → Val T1
    ---
    → CastResult T2
  apply-cast id⋆ v = succ v
  apply-cast (↷ (⁇ l) m t2) (inj P v) = apply-rest (inj₂ (l , l)) m t2 v
  apply-cast (↷ ε m t2) v = apply-rest (inj₁ refl) m t2 v

  apply-rest : ∀ {P1 P2 P3 T}
    → GapP P1 P2
    → Mid P2 P3
    → Tip P3 T
    → Val (` P1)
    ---
    → CastResult T
  apply-rest g m t v with apply-mid g m v
  apply-rest g m t v | succ u = succ (apply-tail t u)
  apply-rest g m t v | fail l = fail l

  apply-tail : ∀ {P T} → Tip P T → Val (` P) → Val T
  apply-tail (⁇ l) v = inj _ v
  apply-tail ε v = v

  apply-mid : ∀ {P1 P2 P3}
    → GapP P1 P2
    → Mid P2 P3
    → Val (` P1)
    ---
    → CastResult (` P3)
  apply-mid {P1} {P2} g m v with (` P1) ⌣? (` P2)
  apply-mid g m v | yes p with m
  apply-mid g m v | yes p | l1 ⊥ l2 = fail l1
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

-- mutual
--   seq-m-assoc : ∀ {P1 P2 P3 P4 P5 P6}
--     → (b1 : Mid P1 P2)
--     → (ℓ1 : GapP P2 P3)
--     → (p1 : (` P2) ⌣ (` P3))
--     → (b2 : Mid P3 P4)
--     → (ℓ2 : GapP P4 P5)
--     → (p2 : (` P4) ⌣ (` P5))
--     → (b3 : Mid P5 P6)
--     ---
--     → seq-m ℓ2 p2 (seq-m ℓ1 p1 b1 b2) b3
--       ≡
--       seq-m ℓ1 p1 b1 (seq-m ℓ2 p2 b2 b3)
--   seq-m-assoc U ℓ1 ⌣U U ℓ2 ⌣U U = refl
--   seq-m-assoc (c₁ ⇒ c₂) ℓ1 ⌣⇒ (c₃ ⇒ c₄) ℓ2 ⌣⇒ (c₅ ⇒ c₆) = cong₂ (λ x y → x ⇒ y) (sym (seq-assoc c₅ (ℓ-dom ℓ2) c₃ (ℓ-dom ℓ1) c₁)) (seq-assoc c₂ (ℓ-cod ℓ1) c₄ (ℓ-cod ℓ2) c₆)
--   seq-m-assoc (c₁ ⊗ c₂) ℓ1 ⌣⊗ (c₃ ⊗ c₄) ℓ2 ⌣⊗ (c₅ ⊗ c₆) = cong₂ (λ x y → x ⊗ y) (seq-assoc c₁ (ℓ-car ℓ1) c₃ (ℓ-car ℓ2) c₅) (seq-assoc c₂ (ℓ-cdr ℓ1) c₄ (ℓ-cdr ℓ2) c₆)
--   seq-m-assoc (c₁ ⊕ c₂) ℓ1 ⌣⊕ (c₃ ⊕ c₄) ℓ2 ⌣⊕ (c₅ ⊕ c₆) = cong₂ (λ x y → x ⊕ y) (seq-assoc c₁ (ℓ-inl ℓ1) c₃ (ℓ-inl ℓ2) c₅) (seq-assoc c₂ (ℓ-inr ℓ1) c₄ (ℓ-inr ℓ2) c₆)
  
--   seq-assoc : ∀ {T1 T2 T3 T4 T5 T6}
--     → (c1 : Cast T1 T2)
--     → (ℓ1 : T2 ≡ T3 ⊎ Label)
--     → (c2 : Cast T3 T4)
--     → (ℓ2 : T4 ≡ T5 ⊎ Label)
--     → (c3 : Cast T5 T6)
--     → seq (seq c1 ℓ1 c2) ℓ2 c3 ≡ seq c1 ℓ1 (seq c2 ℓ2 c3)
--   seq-assoc id⋆ ℓ1 id⋆ ℓ2 id⋆ = refl
--   seq-assoc id⋆ ℓ1 id⋆ ℓ2 (↷ (⁇ l) r) = refl
--   seq-assoc id⋆ ℓ1 id⋆ ℓ2 (↷ ε r) with ℓ2
--   seq-assoc id⋆ ℓ1 id⋆ ℓ2 (↷ ε r) | inj₁ ()
--   seq-assoc id⋆ ℓ1 id⋆ ℓ2 (↷ ε r) | inj₂ y = refl
--   seq-assoc id⋆ ℓ1 (↷ (⁇ l) (rest b (fail l₁))) ℓ2 c3 = refl
--   seq-assoc id⋆ ℓ1 (↷ (⁇ l) (rest b (last t))) ℓ2 id⋆ = refl
--   seq-assoc id⋆ ℓ1 (↷ (⁇ l) (rest {Q = P1} b (last t))) ℓ2 (↷ h (rest {P = P2} b₁ t₁)) with (` P1) ⌣? (` P2)
--   seq-assoc id⋆ ℓ1 (↷ (⁇ l) (rest {Q = P1} b (last t))) ℓ2 (↷ h (rest {_} b₁ t₁)) | yes p = refl
--   seq-assoc id⋆ ℓ1 (↷ (⁇ l) (rest {Q = P1} b (last t))) ℓ2 (↷ h (rest {_} b₁ t₁)) | no ¬p with link h ℓ2 t
--   seq-assoc id⋆ ℓ1 (↷ (⁇ l) (rest {Q = _} b (last t))) ℓ2 (↷ h (rest {_} b₁ t₁)) | no ¬p | inj₁ refl = ⊥-elim (¬p (⌣refl _))
--   seq-assoc id⋆ ℓ1 (↷ (⁇ l) (rest {Q = P1} b (last t))) ℓ2 (↷ h (rest {_} b₁ t₁)) | no ¬p | inj₂ y = refl
--   seq-assoc id⋆ ℓ1 (↷ ε (rest b t)) ℓ2 c3 with ℓ1
--   seq-assoc id⋆ ℓ1 (↷ ε (rest b t)) ℓ2 c3 | inj₁ ()
--   seq-assoc id⋆ ℓ1 (↷ ε (rest b (fail l))) ℓ2 c3 | inj₂ y = refl
--   seq-assoc id⋆ ℓ1 (↷ ε (rest b (last t))) ℓ2 id⋆ | inj₂ y = refl
--   seq-assoc id⋆ ℓ1 (↷ ε (rest {Q = P1} b (last t))) ℓ2 (↷ h (rest {P = P2} b₁ t₁)) | inj₂ y with (` P1) ⌣? (` P2)
--   seq-assoc id⋆ ℓ1 (↷ ε (rest {Q = P1} b (last t))) ℓ2 (↷ h (rest {_} b₁ t₁)) | inj₂ y | yes p = refl
--   seq-assoc id⋆ ℓ1 (↷ ε (rest {Q = P1} b (last t))) ℓ2 (↷ h (rest {_} b₁ t₁)) | inj₂ y | no ¬p with link h ℓ2 t
--   seq-assoc id⋆ ℓ1 (↷ ε (rest {Q = _} b (last t))) ℓ2 (↷ h (rest {_} b₁ t₁)) | inj₂ y | no ¬p | inj₁ refl = ⊥-elim (¬p (⌣refl _))
--   seq-assoc id⋆ ℓ1 (↷ ε (rest {Q = P1} b (last t))) ℓ2 (↷ h (rest {_} b₁ t₁)) | inj₂ y | no ¬p | inj₂ y₁ = refl
--   seq-assoc (↷ h (rest b (fail l))) ℓ1 c2 ℓ2 c3 = refl
--   seq-assoc (↷ h (rest b (last t))) ℓ1 id⋆ ℓ2 id⋆ = refl
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 id⋆ ℓ2 (↷ (⁇ l) (rest {P = P2} b₁ t₁)) with (` P1) ⌣? (` P2)
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 id⋆ ℓ2 (↷ (⁇ l) (rest {_} b₁ t₁)) | yes p = refl
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 id⋆ ℓ2 (↷ (⁇ l) (rest {_} b₁ t₁)) | no ¬p = refl
--   seq-assoc (↷ h (rest b (last t))) ℓ1 id⋆ ℓ2 (↷ ε (rest b₁ t₁)) with ℓ2
--   seq-assoc (↷ h (rest b (last t))) ℓ1 id⋆ ℓ2 (↷ ε (rest b₁ t₁)) | inj₁ ()
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 id⋆ ℓ2 (↷ ε (rest {P = P2} b₁ t₁)) | inj₂ y with (` P1) ⌣? (` P2)
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 id⋆ ℓ2 (↷ ε (rest b₁ t₁)) | inj₂ y | yes p = refl
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 id⋆ ℓ2 (↷ ε (rest b₁ t₁)) | inj₂ y | no ¬p = refl
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {P = P2} b₁ (fail l))) ℓ2 c3 with (` P1) ⌣? (` P2)
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} b₁ (fail l))) ℓ2 c3 | yes p = refl
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} b₁ (fail l))) ℓ2 c3 | no ¬p with link h₁ ℓ1 t
--   seq-assoc (↷ h (rest {Q = _} b (last t))) ℓ1 (↷ h₁ (rest {_} b₁ (fail l))) ℓ2 c3 | no ¬p | inj₁ refl = ⊥-elim (¬p (⌣refl _))
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} b₁ (fail l))) ℓ2 c3 | no ¬p | inj₂ y = refl
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {P = P2} b₁ (last t₁))) ℓ2 id⋆ with (` P1) ⌣? (` P2)
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} b₁ (last t₁))) ℓ2 id⋆ | yes p = refl
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} b₁ (last t₁))) ℓ2 id⋆ | no ¬p with link h₁ ℓ1 t
--   seq-assoc (↷ h (rest {Q = _} b (last t))) ℓ1 (↷ h₁ (rest {_} b₁ (last t₁))) ℓ2 id⋆ | no ¬p | inj₁ refl =  ⊥-elim (¬p (⌣refl (` _)))
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} b₁ (last t₁))) ℓ2 id⋆ | no ¬p | inj₂ y = refl
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {P2} {Q = P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {P = P4} b₂ t₂)) with (` P1) ⌣? (` P2)
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {P4} b₂ t₂)) | yes p with (` P3) ⌣? (` P4)
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {P2} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | yes p | yes p₁ with (` P1) ⌣? (` P2)
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {P2} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {P4} b₂ t₂)) | yes p | yes p₁ | yes p₂
--     rewrite ⌣unique p p₂ = cong (λ b → ↷ h (rest b t₂)) (seq-m-assoc b (link h₁ ℓ1 t) p₂ b₁ (link h₂ ℓ2 t₁) p₁ b₂)
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | yes p | yes p₁ | no ¬p = ⊥-elim (¬p p)
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | yes p | no ¬p with link h₂ ℓ2 t₁
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} {_} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | yes p | no ¬p | inj₁ refl = ⊥-elim (¬p (⌣refl (` _)))
--   seq-assoc (↷ h (rest {Q = .U} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | yes ⌣U | no ¬p | inj₂ y = refl
--   seq-assoc (↷ h (rest {Q = .(_ ⇒ _)} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | yes ⌣⇒ | no ¬p | inj₂ y = refl
--   seq-assoc (↷ h (rest {Q = .(_ ⊗ _)} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | yes ⌣⊗ | no ¬p | inj₂ y = refl
--   seq-assoc (↷ h (rest {Q = .(_ ⊕ _)} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | yes ⌣⊕ | no ¬p | inj₂ y = refl
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {P4} b₂ t₂)) | no ¬p with (` P3) ⌣? (` P4)
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {P2} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | no ¬p | yes p with (` P1) ⌣? (` P2)
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | no ¬p | yes p | yes p₁ = ⊥-elim (¬p p₁)
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | no ¬p | yes p | no ¬p₁ with link h₁ ℓ1 t
--   seq-assoc (↷ h (rest {Q = _} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | no ¬p | yes p | no ¬p₁ | inj₁ refl = ⊥-elim (¬p₁ (⌣refl (` _)))
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | no ¬p | yes p | no ¬p₁ | inj₂ y = refl
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | no ¬p | no ¬p₁ with link h₂ ℓ2 t₁
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} {_} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | no ¬p | no ¬p₁ | inj₁ refl = ⊥-elim (¬p₁ (⌣refl (` _)))
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {P2} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | no ¬p | no ¬p₁ | inj₂ y with (` P1) ⌣? (` P2)
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | no ¬p | no ¬p₁ | inj₂ y | yes p = ⊥-elim (¬p p)
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | no ¬p | no ¬p₁ | inj₂ y | no ¬p₂ with link h₁ ℓ1 t
--   seq-assoc (↷ h (rest {Q = _} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | no ¬p | no ¬p₁ | inj₂ y | no ¬p₂ | inj₁ refl = ⊥-elim (¬p₂ (⌣refl (` _)))
--   seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | no ¬p | no ¬p₁ | inj₂ y | no ¬p₂ | inj₂ y₁ = refl 

-- open import Values Label Cast
  
-- module AlternativeApplyCast where
 
--   apply-body : ∀ {P1 P2 P3}
--     → P1 ≡ P2 ⊎ Label
--     → Mid P2 P3
--     → Val (` P1)
--     → CastResult (` P3)
--   apply-body {P1} {P2} ℓ b v with (` P1) ⌣? (` P2)
--   apply-body {.U} {.U} ℓ U sole | yes ⌣U = succ sole
--   apply-body {.(_ ⇒ _)} {.(_ ⇒ _)} ℓ (c₃ ⇒ c₄) (fun env c₁ b₁ c₂) | yes ⌣⇒ = succ (fun env (seq c₃ (ℓ-dom ℓ) c₁) b₁ (seq c₂ (ℓ-cod ℓ) c₄))
--   apply-body {.(_ ⊗ _)} {.(_ ⊗ _)} ℓ (c₃ ⊗ c₄) (cons v₁ c₁ v₂ c₂) | yes ⌣⊗ = succ (cons v₁ (seq c₁ (ℓ-car ℓ) c₃) v₂ (seq c₂ (ℓ-cdr ℓ) c₄))
--   apply-body {.(_ ⊕ _)} {.(_ ⊕ _)} ℓ (c₃ ⊕ c₄) (inl v c) | yes ⌣⊕ = succ (inl v (seq c (ℓ-inl ℓ) c₃))
--   apply-body {.(_ ⊕ _)} {.(_ ⊕ _)} ℓ (c₃ ⊕ c₄) (inr v c) | yes ⌣⊕ = succ (inr v (seq c (ℓ-inr ℓ) c₄))
--   apply-body {P1} {.P1} (inj₁ refl) b v | no ¬p = ⊥-elim (¬p (⌣refl (` P1)))
--   apply-body {P1} {P2} (inj₂ l) b v | no ¬p = fail l
  
--   apply-tail : ∀ {P T} → Tail P T → Val (` P) → CastResult T
--   apply-tail (fail l) v = fail l
--   apply-tail (last ‼) v = succ (inj _ v)
--   apply-tail (last ε) v = succ v

--   apply-rest : ∀ {P1 P2 T}
--     → GapP P1 P2
--     → Rest P2 T
--     → Val (` P1)
--     ---
--     → CastResult T
--   apply-rest ℓ (rest b t) v = apply-body ℓ b v >>= apply-tail t

--   apply-cast : ∀ {T1 T2}
--     → Cast T1 T2
--     → Val T1
--     ---
--     → CastResult T2
--   apply-cast id⋆ v = succ v
--   apply-cast (↷ (⁇ l) r) (inj _ v) = apply-rest (inj₂ l) r v
--   apply-cast (↷ ε r) v = apply-rest (inj₁ refl) r v

-- open AlternativeApplyCast public

-- mutual
--   lem-id-body : ∀ P
--     → (v : Val (` P))  
--     -----------------------------
--     → apply-body (inj₁ refl) (mk-mid P) v ≡ succ v
--   lem-id-body U sole = refl
--   lem-id-body (T₁ ⇒ T₂) (fun env c₁ b c₂) rewrite seq-id-l c₁ | seq-id-r c₂ = refl
--   lem-id-body (T₁ ⊗ T₂) (cons v c₁ v₁ c₂) rewrite seq-id-r c₁ | seq-id-r c₂ = refl
--   lem-id-body (T₁ ⊕ T₂) (inl v c) rewrite seq-id-r c = refl
--   lem-id-body (T₁ ⊕ T₂) (inr v c) rewrite seq-id-r c = refl

--   lem-id : ∀ T
--     → (v : Val T)  
--     -----------------------------
--     → apply-cast (mk-id T) v ≡ succ v
--   lem-id ⋆ v = refl
--   lem-id (` U) sole = refl
--   lem-id (` (T₁ ⇒ T₂)) (fun env c₁ b c₂) rewrite seq-id-l c₁ | seq-id-r c₂ = refl
--   lem-id (` (T₁ ⊗ T₂)) (cons v c₁ v₁ c₂) rewrite seq-id-r c₁ | seq-id-r c₂ = refl
--   lem-id (` (T₁ ⊕ T₂)) (inl v c) rewrite seq-id-r c = refl
--   lem-id (` (T₁ ⊕ T₂)) (inr v c) rewrite seq-id-r c = refl

-- lem-seq-fail : ∀ {P1 P2 P3 T1 T2}
--   → (v : Val (` P1))
--   → (ℓ : GapP P1 P2)
--   → (b : Mid P2 P3)
--   → (l : Label)
--   → (f : Val T1 → CastResult T2)
--   ---
--   → (apply-body ℓ b v >>= (λ v → fail l)) ≡
--     ((apply-body ℓ b v >>= (λ v → fail l)) >>= f)
-- lem-seq-fail v ℓ b l f with apply-body ℓ b v
-- lem-seq-fail v ℓ b l f | succ v₁ = refl
-- lem-seq-fail v ℓ b l f | fail l₁ = refl

-- lem-apply-body-refl : ∀ {P1 P2}
--   → (v : Val (` P1))
--   → (b : Mid P1 P2)
--   → ∃[ u ](apply-body (inj₁ refl) b v ≡ succ u)
-- lem-apply-body-refl {P1} v b with (` P1) ⌣? (` P1)
-- lem-apply-body-refl {.U} sole U | yes ⌣U = sole , refl
-- lem-apply-body-refl {.(_ ⇒ _)} (fun env c₁ b₁ c₂) (c₃ ⇒ c₄) | yes ⌣⇒
--   = (fun env (seq c₃ (inj₁ refl) c₁) b₁ (seq c₂ (inj₁ refl) c₄)) , refl
-- lem-apply-body-refl {.(_ ⊗ _)} (cons v c₁ v₁ c₂) (c₃ ⊗ c₄) | yes ⌣⊗
--   = cons v (seq c₁ (inj₁ refl) c₃) v₁ (seq c₂ (inj₁ refl) c₄) , refl
-- lem-apply-body-refl {.(_ ⊕ _)} (inl v c) (c₁ ⊕ c₂) | yes ⌣⊕ = inl v (seq c (inj₁ refl) c₁) , refl
-- lem-apply-body-refl {.(_ ⊕ _)} (inr v c) (c₁ ⊕ c₂) | yes ⌣⊕ = inr v (seq c (inj₁ refl) c₂) , refl
-- lem-apply-body-refl {P1} v b | no ¬p = ⊥-elim (¬p (⌣refl _))

-- lem-apply-body-⌣ : ∀ {P0 P1 P2}
--   → (v : Val (` P0))
--   → (ℓ : GapP P0 P1)
--   → (p : (` P0) ⌣ (` P1))
--   → (b : Mid P1 P2)
--   → ∃[ u ](apply-body ℓ b v ≡ succ u)
-- lem-apply-body-⌣ {.U} {.U} sole ℓ ⌣U U = sole , refl
-- lem-apply-body-⌣ {.(_ ⇒ _)} {.(_ ⇒ _)} (fun env c₁ b₁ c₂) ℓ ⌣⇒ (c₃ ⇒ c₄) = (fun env (seq c₃ _ c₁) b₁ (seq c₂ _ c₄)) , refl
-- lem-apply-body-⌣ {.(_ ⊗ _)} {.(_ ⊗ _)} (cons v c₁ v₁ c₂) ℓ ⌣⊗ (c₃ ⊗ c₄) = cons v (seq c₁ _ c₃) v₁ (seq c₂ _ c₄) , refl
-- lem-apply-body-⌣ {.(_ ⊕ _)} {.(_ ⊕ _)} (inl v c) ℓ ⌣⊕ (c₁ ⊕ c₂) = inl v (seq c _ c₁) , refl
-- lem-apply-body-⌣ {.(_ ⊕ _)} {.(_ ⊕ _)} (inr v c) ℓ ⌣⊕ (c₁ ⊕ c₂) = inr v (seq c _ c₂) , refl

-- lem-seq' : ∀ {P1 P2 P3 P4 P5 T1 T2}
--   → (v : Val (` P1))
--   → (ℓ : GapP P1 P2)
--   → (b1 : Mid P2 P3)
--   → (t1 : Tip P3 T1)
--   → (h2 : Tip P4 T1)
--   → (b2 : Mid P4 P5)
--   → (t2 : Tail P5 T2)
--   → apply-rest ℓ
--       (seq-rest b1 t1 (inj₁ refl) h2 (rest b2 t2))
--       v
--     ≡
--     ((apply-body ℓ b1 v >>= apply-tail (last t1)) >>=
--       apply-cast (↷ h2 (rest b2 t2)))
-- lem-seq' {P1} {P2} {P3} {P4} v ℓ b1 t1 h2 b2 t2 with (` P3) ⌣? (` P4)
-- lem-seq' {P1} {P2} {P3} {P4} v ℓ b1 t1 h2 b2 t2 | yes p with t1 | h2
-- lem-seq' {P1} {P2} {P3} {P4} v ℓ b1 t1 h2 b2 t2 | yes p | ‼ | ⁇ l with (` P1) ⌣? (` P2)
-- lem-seq' {.U} {.U} {.U} {.U} sole ℓ U t1 h2 U t2 | yes ⌣U | ‼ | ⁇ l | yes ⌣U = refl
-- lem-seq' {.(_ ⇒ _)} {.(_ ⇒ _)} {.(_ ⇒ _)} {.(_ ⇒ _)} (fun env c₁ b c₂) ℓ (c₃ ⇒ c₄) t1 h2 (c₅ ⇒ c₆) t2 | yes ⌣⇒ | ‼ | ⁇ l | yes ⌣⇒
--   rewrite seq-assoc c₅ (inj₂ l) c₃ (ℓ-dom ℓ) c₁ | seq-assoc c₂ (ℓ-cod ℓ) c₄ (inj₂ l) c₆
--   = refl
-- lem-seq' {.(_ ⊗ _)} {.(_ ⊗ _)} {.(_ ⊗ _)} {.(_ ⊗ _)} (cons v c₁ v₁ c₂) ℓ (c₃ ⊗ c₄) t1 h2 (c₅ ⊗ c₆) t2 | yes ⌣⊗ | ‼ | ⁇ l | yes ⌣⊗
--   rewrite seq-assoc c₁ (ℓ-car ℓ) c₃ (inj₂ l) c₅ | seq-assoc c₂ (ℓ-cdr ℓ) c₄ (inj₂ l) c₆
--   = refl
-- lem-seq' {.(_ ⊕ _)} {.(_ ⊕ _)} {.(_ ⊕ _)} {.(_ ⊕ _)} (inl v c) ℓ (c₁ ⊕ c₂) t1 h2 (c₃ ⊕ c₄) t2 | yes ⌣⊕ | ‼ | ⁇ l | yes ⌣⊕
--   rewrite seq-assoc c (ℓ-inl ℓ) c₁ (inj₂ l) c₃
--   = refl
-- lem-seq' {.(_ ⊕ _)} {.(_ ⊕ _)} {.(_ ⊕ _)} {.(_ ⊕ _)} (inr v c) ℓ (c₁ ⊕ c₂) t1 h2 (c₃ ⊕ c₄) t2 | yes ⌣⊕ | ‼ | ⁇ l | yes ⌣⊕
--   rewrite seq-assoc c (ℓ-inr ℓ) c₂ (inj₂ l) c₄
--   = refl
-- lem-seq' {P1} {.P1} {P3} {P4} v (inj₁ refl) b1 t1 h2 b2 t2 | yes p | ‼ | ⁇ l | no ¬p = (⊥-elim (¬p (⌣refl (` P1))))
-- lem-seq' {P1} {P2} {P3} {P4} v (inj₂ y) b1 t1 h2 b2 t2 | yes p | ‼ | ⁇ l | no ¬p = refl
-- lem-seq' {P1} {P2} {P3} {P4} v ℓ b1 t1 h2 b2 t2 | yes p | ε | ε with (` P1) ⌣? (` P2)
-- lem-seq' {.(_ ⇒ _)} {.(_ ⇒ _)} {.(_ ⇒ _)} {.(_ ⇒ _)} (fun env c₁ b c₂) ℓ (c₃ ⇒ c₄) t1 h2 (c₅ ⇒ c₆) t2 | yes ⌣⇒ | ε | ε | yes ⌣⇒
--   rewrite seq-assoc c₅ (inj₁ refl) c₃ (ℓ-dom ℓ) c₁ | seq-assoc c₂ (ℓ-cod ℓ) c₄ (inj₁ refl) c₆
--   = refl
-- lem-seq' {.U} {.U} {.U} {.U} sole ℓ U t1 h2 U t2 | yes ⌣U | ε | ε | yes ⌣U = refl
-- lem-seq' {.(_ ⊗ _)} {.(_ ⊗ _)} {.(_ ⊗ _)} {.(_ ⊗ _)} (cons v c₁ v₁ c₂) ℓ (c₃ ⊗ c₄) t1 h2 (c₅ ⊗ c₆) t2 | yes ⌣⊗ | ε | ε | yes ⌣⊗
--   rewrite seq-assoc c₁ (ℓ-car ℓ) c₃ (inj₁ refl) c₅ | seq-assoc c₂ (ℓ-cdr ℓ) c₄ (inj₁ refl) c₆
--   = refl
-- lem-seq' {.(_ ⊕ _)} {.(_ ⊕ _)} {.(_ ⊕ _)} {.(_ ⊕ _)} (inl v c) ℓ (c₁ ⊕ c₂) t1 h2 (c₃ ⊕ c₄) t2 | yes ⌣⊕ | ε | ε | yes ⌣⊕
--   rewrite seq-assoc c (ℓ-inl ℓ) c₁ (inj₁ refl) c₃
--   = refl
-- lem-seq' {.(_ ⊕ _)} {.(_ ⊕ _)} {.(_ ⊕ _)} {.(_ ⊕ _)} (inr v c) ℓ (c₁ ⊕ c₂) t1 h2 (c₃ ⊕ c₄) t2 | yes ⌣⊕ | ε | ε | yes ⌣⊕
--   rewrite seq-assoc c (ℓ-inr ℓ) c₂ (inj₁ refl) c₄
--   = refl
-- lem-seq' {P1} {.P1} {P3} {P3} v (inj₁ refl) b1 t1 h2 b2 t2 | yes p | ε | ε | no ¬p = (⊥-elim (¬p (⌣refl (` P1))))
-- lem-seq' {P1} {P2} {P3} {P3} v (inj₂ y) b1 t1 h2 b2 t2 | yes p | ε | ε | no ¬p = refl
-- lem-seq' {P1} {P2} {P3} {P4} v ℓ b1 t1 h2 b2 t2 | no ¬p with t1 | h2
-- ... | ε | ε = (⊥-elim (¬p (⌣refl (` P3))))
-- ... | ‼ | ⁇ l with apply-body ℓ b1 v
-- lem-seq' {P1} {P2} {P3} {P4} v ℓ b1 t1 h2 b2 t2 | no ¬p | ‼ | ⁇ l | succ v₁ with (` P3) ⌣? (` P4)
-- lem-seq' {P1} {P2} {P3} {P4} v ℓ b1 t1 h2 b2 t2 | no ¬p | ‼ | ⁇ l | succ v₁ | yes p = ⊥-elim (¬p p)
-- lem-seq' {P1} {P2} {P3} {P4} v ℓ b1 t1 h2 b2 t2 | no ¬p | ‼ | ⁇ l | succ v₁ | no ¬p₁ = refl
-- lem-seq' {P1} {P2} {P3} {P4} v ℓ b1 t1 h2 b2 t2 | no ¬p | ‼ | ⁇ l | fail l₁ = refl

-- lem-seq : ∀ {T1 T2 T3}
--   → (c1 : Cast T1 T2)
--   → (c2 : Cast T2 T3)
--   → (v : Val T1)
--   --------------------
--   → apply-cast (mk-seq c1 c2) v ≡ apply-cast c1 v >>= λ u → apply-cast c2 u
-- lem-seq id⋆ id⋆ v = refl
-- lem-seq id⋆ (↷ (⁇ l) r) v = refl
-- lem-seq (↷ h (rest b (last ‼))) id⋆ v = sym (>>=-succ _)
-- lem-seq (↷ (⁇ l₁) (rest b (fail l))) c2 (inj P v) = lem-seq-fail v (inj₂ l₁) b l _
-- lem-seq (↷ ε (rest b (fail l))) c2 v = lem-seq-fail v _ b l _
-- lem-seq (↷ (⁇ l) (rest {Q = P1} b (last t))) (↷ h₁ (rest {_} b₁ t₁)) (inj P v) = lem-seq' v (inj₂ l) b t h₁ b₁ t₁
-- lem-seq (↷ ε (rest {Q = P1} b (last t))) (↷ h₁ (rest {_} b₁ t₁)) v = lem-seq' v (inj₁ refl) b t h₁ b₁ t₁

-- lem-cast-¬⌣ : ∀ {T1 T2}
--   → (l : Label)
--   → ¬ (T1 ⌣ T2)
--   → (v : Val T1)
--   → apply-cast (mk-cast l T1 T2) v ≡ fail l
-- lem-cast-¬⌣ {⋆} {⋆} l ¬p v = ⊥-elim (¬p ⋆⌣⋆)
-- lem-cast-¬⌣ {⋆} {` P} l ¬p v = ⊥-elim (¬p (⋆⌣P P))
-- lem-cast-¬⌣ {` P} {⋆} l ¬p v = ⊥-elim (¬p (P⌣⋆ P))
-- lem-cast-¬⌣ {` P} {` P₁} l ¬p v with (` P) ⌣? (` P₁)
-- lem-cast-¬⌣ {` P} {` P₁} l ¬p v | yes p = ⊥-elim (¬p p)
-- lem-cast-¬⌣ {` P} {` P₁} l ¬p v | no ¬p₁
--   rewrite sym (>>=-succ (apply-body (inj₁ refl) (mk-mid P) v))
--         | lem-id (` P) v
--   = refl

-- lem-cast-id⋆ : ∀ l
--   → (v : Val ⋆)
--   → apply-cast (mk-cast l ⋆ ⋆) v ≡ succ v
-- lem-cast-id⋆ l v = refl

-- lem-cast-inj : ∀ {P}
--   → (l : Label)
--   → (v : Val (` P))  
--   → apply-cast (mk-cast l (` P) ⋆) v ≡ succ (inj P v)
-- lem-cast-inj {P} l v
--   rewrite sym (>>=-succ (apply-body (inj₁ refl) (mk-mid P) v))
--         | lem-id (` P) v
--   = refl

-- lem-seq2-id : ∀ {T1 T2 T3 T4}
--   → (c1 : Cast T1 T2)
--   → (ℓ : GapT T2 T3)
--   → (c2 : Cast T3 T4)
--   → seq c1 (inj₁ refl) (seq (mk-id T2) ℓ c2)
--     ≡ seq c1 ℓ c2
-- lem-seq2-id c1 ℓ c2
--   rewrite sym (seq-assoc c1 (inj₁ refl) (mk-id _) ℓ c2) | seq-id-r c1
--   = refl

-- lem-cast-proj : ∀ l P P₁ v
--   → apply-cast (mk-cast l ⋆ (` P)) (inj P₁ v) ≡ apply-cast (mk-cast l (` P₁) (` P)) v
-- lem-cast-proj l P P₁ v with (` P₁) ⌣? (` P)
-- lem-cast-proj l .U .U sole | yes ⌣U = refl
-- lem-cast-proj l (T1 ⇒ T2) (T3 ⇒ T4) (fun env c₁ b c₂) | yes ⌣⇒
--   rewrite seq-id-l (seq (mk-id T1) (inj₂ l) c₁)
--         | seq-assoc (mk-id T1) (inj₂ l) (mk-id T3) (inj₁ refl) c₁
--         | seq-id-l c₁
--         | seq-id-r (seq c₂ (inj₂ l) (mk-id T2))
--         | sym (seq-assoc c₂ (inj₁ refl) (mk-id T4) (inj₂ l) (mk-id T2))
--         | seq-id-r c₂
--   = refl
-- lem-cast-proj l (T1 ⊗ T2) (T3 ⊗ T4) (cons v c₁ v₁ c₂) | yes ⌣⊗
--   rewrite lem-seq2-id c₁ (inj₂ l) (mk-id T1) | lem-seq2-id c₂ (inj₂ l) (mk-id T2)
--   = refl
-- lem-cast-proj l (T1 ⊕ T2) (T3 ⊕ T4) (inl v c₁) | yes ⌣⊕
--   rewrite lem-seq2-id c₁ (inj₂ l) (mk-id T1)
--   = refl
-- lem-cast-proj l (T1 ⊕ T2) (T3 ⊕ T4) (inr v c₂) | yes ⌣⊕
--   rewrite lem-seq2-id c₂ (inj₂ l) (mk-id T2)
--   = refl
-- lem-cast-proj l P P₁ v | no ¬p rewrite lem-id-body P₁ v = refl

-- lem-cast-U : ∀ l
--   → apply-cast (mk-cast l (` U) (` U)) sole ≡ succ sole
-- lem-cast-U l = refl

-- lem-cast-⇒ : ∀ T11 T12 T21 T22
--   → ∀ {S T}
--   → (l : Label)
--   → {Γ : Context}
--   → (E : Env Γ)
--   → (c₁ : Cast T11 S)
--   → (b : (Γ , S) ⊢ T)
--   → (c₂ : Cast T T12)
--   → apply-cast (mk-cast l (` (T11 ⇒ T12)) (` (T21 ⇒ T22))) (fun E c₁ b c₂) ≡
--     succ (fun E (mk-seq (mk-cast l T21 T11) c₁) b (mk-seq c₂ (mk-cast l T12 T22)))
-- lem-cast-⇒ T11 T12 T21 T22 l E c₁ b c₂ = refl

-- lem-cast-⊗ : ∀ T01 T02 T11 T12 T21 T22
--   → (l : Label)
--   → (v₁ : Val T01)
--   → (v₂ : Val T02)
--   → (c₁ : Cast T01 T11)
--   → (c₂ : Cast T02 T12)
--   → apply-cast (mk-cast l (` (T11 ⊗ T12)) (` (T21 ⊗ T22))) (cons v₁ c₁ v₂ c₂) ≡
--     succ (cons v₁ (mk-seq c₁ (mk-cast l T11 T21)) v₂ (mk-seq c₂ (mk-cast l T12 T22)))
-- lem-cast-⊗ T01 T02 T11 T12 T21 T22 l v₁ v₂ c₁ c₂ = refl
    
-- lem-cast-⊕-l : ∀ T T11 T12 T21 T22
--   → (l : Label)
--   → (v : Val T)
--   → (c : Cast T T11)
--   → apply-cast (mk-cast l (` (T11 ⊕ T12)) (` (T21 ⊕ T22))) (inl v c) ≡
--     succ (inl v (mk-seq c (mk-cast l T11 T21)))
-- lem-cast-⊕-l T T11 T12 T21 T22 l v c = refl

-- lem-cast-⊕-r : ∀ T T11 T12 T21 T22
--   → (l : Label)
--   → (v : Val T)
--   → (c : Cast T T12)
--   → apply-cast (mk-cast l (` (T11 ⊕ T12)) (` (T21 ⊕ T22))) (inr v c) ≡
--     succ (inr v (mk-seq c (mk-cast l T12 T22)))
-- lem-cast-⊕-r T T11 T12 T21 T22 l v c = refl

-- cast-adt : CastADT
-- cast-adt
--   = record
--     { Cast = Cast
--     ; mk-cast = mk-cast
--     ; mk-seq = mk-seq
--     ; mk-id = mk-id
--     ; apply-cast = apply-cast
--     }
-- cast-adt-LazyD : LazyD cast-adt
-- cast-adt-LazyD
--   = record
--     { lem-id = lem-id
--     ; lem-seq = lem-seq
--     ; lem-cast-¬⌣ = lem-cast-¬⌣
--     ; lem-cast-id⋆ = lem-cast-id⋆
--     ; lem-cast-inj = lem-cast-inj
--     ; lem-cast-proj = lem-cast-proj
--     ; lem-cast-U = lem-cast-U
--     ; lem-cast-⇒ = lem-cast-⇒
--     ; lem-cast-⊗ = lem-cast-⊗
--     ; lem-cast-⊕-l = lem-cast-⊕-l
--     ; lem-cast-⊕-r = lem-cast-⊕-r
--     }
-- cast-adt-monoid : Monoid cast-adt
-- cast-adt-monoid
--   = record
--     { lem-id-l = seq-id-l
--     ; lem-id-r = seq-id-r
--     ; lem-assoc = λ c1 c2 c3 → seq-assoc c1 _ c2 _ c3
--     }

-- lem-cast-id-is-id : ∀ l T →
--   mk-cast l T T ≡ mk-id T
-- lem-cast-id-is-id l ⋆ = refl
-- lem-cast-id-is-id l (` U) = refl
-- lem-cast-id-is-id l (` (T₁ ⇒ T₂))
--   rewrite lem-cast-id-is-id l T₁ | lem-cast-id-is-id l T₂ = refl
-- lem-cast-id-is-id l (` (T₁ ⊗ T₂))
--   rewrite lem-cast-id-is-id l T₁ | lem-cast-id-is-id l T₂ = refl
-- lem-cast-id-is-id l (` (T₁ ⊕ T₂))
--   rewrite lem-cast-id-is-id l T₁ | lem-cast-id-is-id l T₂ = refl

-- cast-adt-cast-id-is-id : CastIdIsId cast-adt
-- cast-adt-cast-id-is-id
--   = record { lem-cast-id-is-id = lem-cast-id-is-id }
