module ReversibleHypercoercions (Label : Set) where

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

thm-seq-rev : ∀ {R S T}
  → (c1 : Cast R S)
  → (c2 : Cast S T)
  ---
  → mk-rev (mk-seq (mk-rev c2) (mk-rev c1)) ≡ mk-seq c1 c2
thm-seq-rev c1 c2 = lem-seq-rev c1 _ c2

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
  apply-cast (↷ (⁇ l) m t2) (dyn v) = apply-rest (inj₂ (l , l)) m t2 v
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
  apply-tail (⁇ l) v = dyn v
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
