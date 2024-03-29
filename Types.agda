module Types where
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

infix 100 _⇒_
infix 100 _⊗_
infix 100 _⊕_

mutual
  data Type : Set where
    ⋆ : Type
    `_ : (P : PreType) → Type
    
  data PreType : Set where
    U : PreType -- the unit type, adding other base type should be straightforward
    _⇒_ : (T₁ T₂ : Type) → PreType
    _⊗_ : (T₁ T₂ : Type) → PreType
    _⊕_ : (T₁ T₂ : Type) → PreType
    ref : (T₁ : Type) → PreType


mutual
  _≡?_ : (T1 T2 : Type) → Dec (T1 ≡ T2)
  ⋆ ≡? ⋆ = yes refl
  ⋆ ≡? (` P) = no (λ ())
  (` P) ≡? ⋆ = no (λ ())
  (` U) ≡? (` U) = yes refl
  (` U) ≡? (` (T₁ ⇒ T₂)) = no (λ ())
  (` U) ≡? (` (T₁ ⊗ T₂)) = no (λ ())
  (` U) ≡? (` (T₁ ⊕ T₂)) = no (λ ())
  (` (T₁ ⇒ T₂)) ≡? (` U) = no (λ ())
  (` (T₁ ⇒ T₂)) ≡? (` (T₃ ⇒ T₄)) with T₁ ≡? T₃ | T₂ ≡? T₄
  ((` (T₁ ⇒ T₂)) ≡? (` (.T₁ ⇒ .T₂))) | yes refl | yes refl = yes refl
  ((` (T₁ ⇒ T₂)) ≡? (` (.T₁ ⇒ T₄))) | yes refl | no ¬p = no λ { refl → ¬p refl }
  ((` (T₁ ⇒ T₂)) ≡? (` (T₃ ⇒ T₄))) | no ¬p | p2 = no λ { refl → ¬p refl }
  (` (T₁ ⇒ T₂)) ≡? (` (T₃ ⊗ T₄)) = no (λ ())
  (` (T₁ ⇒ T₂)) ≡? (` (T₃ ⊕ T₄)) = no (λ ())
  (` (T₁ ⊗ T₂)) ≡? (` U) = no (λ ())
  (` (T₁ ⊗ T₂)) ≡? (` (T₃ ⇒ T₄)) = no (λ ())
  (` (T₁ ⊗ T₂)) ≡? (` (T₃ ⊗ T₄)) with T₁ ≡? T₃ | T₂ ≡? T₄
  ((` (T₁ ⊗ T₂)) ≡? (` (.T₁ ⊗ .T₂))) | yes refl | yes refl = yes refl
  ((` (T₁ ⊗ T₂)) ≡? (` (.T₁ ⊗ T₄))) | yes refl | no ¬p = no λ { refl → ¬p refl }
  ((` (T₁ ⊗ T₂)) ≡? (` (T₃ ⊗ T₄))) | no ¬p | p2 = no λ { refl → ¬p refl }
  (` (T₁ ⊗ T₂)) ≡? (` (T₃ ⊕ T₄)) = no (λ ())
  (` (T₁ ⊕ T₂)) ≡? (` U) = no (λ ())
  (` (T₁ ⊕ T₂)) ≡? (` (T₃ ⇒ T₄)) = no (λ ())
  (` (T₁ ⊕ T₂)) ≡? (` (T₃ ⊗ T₄)) = no (λ ())
  (` (T₁ ⊕ T₂)) ≡? (` (T₃ ⊕ T₄)) with T₁ ≡? T₃ | T₂ ≡? T₄
  ((` (T₁ ⊕ T₂)) ≡? (` (T₃ ⊕ T₄))) | yes refl | yes refl = yes refl
  ((` (T₁ ⊕ T₂)) ≡? (` (T₃ ⊕ T₄))) | yes refl | no ¬p = no λ { refl → ¬p refl }
  ((` (T₁ ⊕ T₂)) ≡? (` (T₃ ⊕ T₄))) | no ¬p | p2 = no λ { refl → ¬p refl }
  (` U) ≡? (` ref T₁) = no (λ ())
  (` (T₁ ⇒ T₂)) ≡? (` ref T₃) = no (λ ())
  (` (T₁ ⊗ T₂)) ≡? (` ref T₃) = no (λ ())
  (` (T₁ ⊕ T₂)) ≡? (` ref T₃) = no (λ ())
  (` ref T₁) ≡? (` U) = no (λ ())
  (` ref T₁) ≡? (` (T₂ ⇒ T₃)) = no (λ ())
  (` ref T₁) ≡? (` (T₂ ⊗ T₃)) = no (λ ())
  (` ref T₁) ≡? (` (T₂ ⊕ T₃)) = no (λ ())
  (` ref T₁) ≡? (` ref T₂) with T₁ ≡? T₂
  ((` ref T₁) ≡? (` ref .T₁)) | yes refl = yes refl
  ((` ref T₁) ≡? (` ref T₂)) | no ¬p = no λ { refl → ¬p refl }
  
-- shallow consistency

data _⌣_ : (T1 T2 : Type) → Set where
  ⋆⌣⋆ : ⋆ ⌣ ⋆
  ⋆⌣P : ∀ P → ⋆ ⌣ (` P)
  P⌣⋆ : ∀ P → (` P) ⌣ ⋆
  ⌣U : (` U) ⌣ (` U)
  ⌣⇒ : ∀ {T1 T2 T3 T4} → (` T1 ⇒ T2) ⌣ (` T3 ⇒ T4)
  ⌣⊗ : ∀ {T1 T2 T3 T4} → (` T1 ⊗ T2) ⌣ (` T3 ⊗ T4)
  ⌣⊕ : ∀ {T1 T2 T3 T4} → (` T1 ⊕ T2) ⌣ (` T3 ⊕ T4)
  ⌣! : ∀ {T1 T2} → (` ref T1) ⌣ (` ref T2)

_⌣?_ : ∀ T1 T2 → Dec (T1 ⌣ T2)
⋆ ⌣? ⋆ = yes ⋆⌣⋆
⋆ ⌣? (` P) = yes (⋆⌣P P)
(` P) ⌣? ⋆ = yes (P⌣⋆ P)
(` U) ⌣? (` U) = yes ⌣U
(` U) ⌣? (` (T₁ ⇒ T₂)) = no (λ ())
(` U) ⌣? (` (T₁ ⊗ T₂)) = no (λ ())
(` U) ⌣? (` (T₁ ⊕ T₂)) = no (λ ())
(` (T₁ ⇒ T₂)) ⌣? (` U) = no (λ ())
(` (T₁ ⇒ T₂)) ⌣? (` (T₃ ⇒ T₄)) = yes ⌣⇒
(` (T₁ ⇒ T₂)) ⌣? (` (T₃ ⊗ T₄)) = no (λ ())
(` (T₁ ⇒ T₂)) ⌣? (` (T₃ ⊕ T₄)) = no (λ ())
(` (T₁ ⊗ T₂)) ⌣? (` U) = no (λ ())
(` (T₁ ⊗ T₂)) ⌣? (` (T₃ ⇒ T₄)) = no (λ ())
(` (T₁ ⊗ T₂)) ⌣? (` (T₃ ⊗ T₄)) = yes ⌣⊗
(` (T₁ ⊗ T₂)) ⌣? (` (T₃ ⊕ T₄)) = no (λ ())
(` (T₁ ⊕ T₂)) ⌣? (` U) = no (λ ())
(` (T₁ ⊕ T₂)) ⌣? (` (T₃ ⇒ T₄)) = no (λ ())
(` (T₁ ⊕ T₂)) ⌣? (` (T₃ ⊗ T₄)) = no (λ ())
(` (T₁ ⊕ T₂)) ⌣? (` (T₃ ⊕ T₄)) = yes ⌣⊕
(` U) ⌣? (` ref T₁) = no (λ ())
(` (T₂ ⇒ T₃)) ⌣? (` ref T₁) = no (λ ())
(` (T₂ ⊗ T₃)) ⌣? (` ref T₁) = no (λ ())
(` (T₂ ⊕ T₃)) ⌣? (` ref T₁) = no (λ ())
(` ref T₁) ⌣? (` U) = no (λ ())
(` ref T₃) ⌣? (` (T₁ ⇒ T₂)) = no (λ ())
(` ref T₃) ⌣? (` (T₁ ⊗ T₂)) = no (λ ())
(` ref T₃) ⌣? (` (T₁ ⊕ T₂)) = no (λ ())
(` ref T₂) ⌣? (` ref T₁) = yes ⌣!

⌣refl : ∀ T → T ⌣ T
⌣refl ⋆ = ⋆⌣⋆
⌣refl (` U) = ⌣U
⌣refl (` (T₁ ⇒ T₂)) = ⌣⇒
⌣refl (` (T₁ ⊗ T₂)) = ⌣⊗
⌣refl (` (T₁ ⊕ T₂)) = ⌣⊕
⌣refl (` (ref T₁)) = ⌣!

⌣symm : ∀ {S T} → S ⌣ T → T ⌣ S
⌣symm ⋆⌣⋆ = ⋆⌣⋆
⌣symm (⋆⌣P P) = P⌣⋆ P
⌣symm (P⌣⋆ P) = ⋆⌣P P
⌣symm ⌣U = ⌣U
⌣symm ⌣⇒ = ⌣⇒
⌣symm ⌣⊗ = ⌣⊗
⌣symm ⌣⊕ = ⌣⊕
⌣symm ⌣! = ⌣!


⌣unique : ∀ {T1 T2}
  → (p1 p2 : T1 ⌣ T2)
  ---
  → p1 ≡ p2
⌣unique ⋆⌣⋆ ⋆⌣⋆ = refl
⌣unique (⋆⌣P P) (⋆⌣P .P) = refl
⌣unique (P⌣⋆ P) (P⌣⋆ .P) = refl
⌣unique ⌣U ⌣U = refl
⌣unique ⌣⇒ ⌣⇒ = refl
⌣unique ⌣⊗ ⌣⊗ = refl
⌣unique ⌣⊕ ⌣⊕ = refl
⌣unique ⌣! ⌣! = refl

-- subtype

data _≤_ : Type → Type → Set where

  ⋆≤⋆ : ⋆ ≤ ⋆
  
  P≤⋆ : ∀ P → (` P) ≤ ⋆
  
  ≤U : (` U) ≤ (` U)
  
  ≤⇒ : ∀ {T1 T2 T3 T4}
    → T3 ≤ T1
    → T2 ≤ T4
    ---
    → (` T1 ⇒ T2) ≤ (` T3 ⇒ T4)
    
  ≤⊗ : ∀ {T1 T2 T3 T4}
    → T1 ≤ T3
    → T2 ≤ T4
    ---
    → (` T1 ⊗ T2) ≤ (` T3 ⊗ T4)
    
  ≤⊕ : ∀ {T1 T2 T3 T4}
    → T1 ≤ T3
    → T2 ≤ T4
    ---
    → (` T1 ⊕ T2) ≤ (` T3 ⊕ T4)

-- imprecise

data _⊑_ : Type → Type → Set where

  ⋆⊑⋆ : ⋆ ⊑ ⋆
  
  P⊑⋆ : ∀ P → (` P) ⊑ ⋆
  
  ⊑U : (` U) ⊑ (` U)
  
  ⊑⇒ : ∀ {T1 T2 T3 T4}
    → T1 ⊑ T3
    → T2 ⊑ T4
    ---
    → (` T1 ⇒ T2) ⊑ (` T3 ⇒ T4)
    
  ⊑⊗ : ∀ {T1 T2 T3 T4}
    → T1 ⊑ T3
    → T2 ⊑ T4
    ---
    → (` T1 ⊗ T2) ⊑ (` T3 ⊗ T4)
    
  ⊑⊕ : ∀ {T1 T2 T3 T4}
    → T1 ⊑ T3
    → T2 ⊑ T4
    ---
    → (` T1 ⊕ T2) ⊑ (` T3 ⊕ T4)

  
