
module plfa.part2.Fun where

open import Agda.Builtin.Nat renaming (Nat to ℕ; zero to zℕ ; suc to sℕ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.String using (String; _≟_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Relation.Nullary using (¬_; Dec; yes; no)

infix  4  _∋_⦂_
infix  4  _⊢_↑_
infix  4  _⊢_↓_
infixl 5  _,_⦂_

infixr 7  _⇒_

infix  5  ƛ_⇒_
infix  6  _↑
infix  6  _↓_
infixl 7  _·_
infix  9  `_

Id : Set
Id = String

_≠_ : ∀ (x y : Id) → x ≢ y
x ≠ y  with x ≟ y
...       | no  x≢y  =  x≢y
...       | yes _    =  ⊥-elim impossible
  where postulate impossible : ⊥

data Type : Set where
  o    : Type
  _⇒_  : Type → Type → Type

o≢⇒ : ∀ {A B} → o ≢ A ⇒ B
o≢⇒ ()

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context

data Term⁺ : Set
data Term⁻ : Set

data Term⁺ where
  `_  : Id → Term⁺
  _·_ : Term⁺ → Term⁻ → Term⁺
  _↓_ : Term⁻ → Type → Term⁺

data Term⁻ where
  ƛ_⇒_ : Id → Term⁻ → Term⁻
  _↑   : Term⁺ → Term⁻

data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
      --------------------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
      -----------------
    → Γ , y ⦂ B ∋ x ⦂ A

uniq-∋ : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
uniq-∋ Z Z                 =  refl
uniq-∋ Z (S x≢y _)         =  ⊥-elim (x≢y refl)
uniq-∋ (S x≢y _) Z         =  ⊥-elim (x≢y refl)
uniq-∋ (S _ ∋x) (S _ ∋x′)  =  uniq-∋ ∋x ∋x′

data _⊢_↑_ : Context → Term⁺ → Type → Set
data _⊢_↓_ : Context → Term⁻ → Type → Set

data _⊢_↑_ where

  ⊢` : ∀ {Γ A x}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ↑ A

  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ↑ A ⇒ B
    → Γ ⊢ M ↓ A
      -------------
    → Γ ⊢ L · M ↑ B

  ⊢↓ : ∀ {Γ M A}
    → Γ ⊢ M ↓ A
      ---------------
    → Γ ⊢ (M ↓ A) ↑ A

data _⊢_↓_ where

  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ↓ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ↓ A ⇒ B

  ⊢↑ : ∀ {Γ M A B}
    → Γ ⊢ M ↑ A
    → A ≡ B
      -------------
    → Γ ⊢ (M ↑) ↓ B

_≟Tp_ : (A B : Type) → Dec (A ≡ B)
o      ≟Tp o              =  yes refl
o      ≟Tp (A ⇒ B)         =  no λ()
(A ⇒ B) ≟Tp o              =  no λ()
(A ⇒ B) ≟Tp (A′ ⇒ B′)
  with A ≟Tp A′ | B ≟Tp B′
...  | no A≢    | _         =  no λ{refl → A≢ refl}
...  | yes _    | no B≢     =  no λ{refl → B≢ refl}
...  | yes refl | yes refl  =  yes refl

dom≡ : ∀ {A A′ B B′} → A ⇒ B ≡ A′ ⇒ B′ → A ≡ A′
dom≡ refl = refl

rng≡ : ∀ {A A′ B B′} → A ⇒ B ≡ A′ ⇒ B′ → B ≡ B′
rng≡ refl = refl

uniq-↑ : ∀ {Γ M A B} → Γ ⊢ M ↑ A → Γ ⊢ M ↑ B → A ≡ B
uniq-↑ (⊢` ∋x) (⊢` ∋x′)       =  uniq-∋ ∋x ∋x′
uniq-↑ (⊢L · ⊢M) (⊢L′ · ⊢M′)  =  rng≡ (uniq-↑ ⊢L ⊢L′)
uniq-↑ (⊢↓ ⊢M) (⊢↓ ⊢M′)       =  refl

¬arg : ∀ {Γ A B L M}
  → Γ ⊢ L ↑ A ⇒ B
  → ¬ Γ ⊢ M ↓ A
    -------------------------
  → ¬ ∃[ B′ ](Γ ⊢ L · M ↑ B′)
¬arg ⊢L ¬⊢M ⟨ B′ , ⊢L′ · ⊢M′ ⟩ rewrite dom≡ (uniq-↑ ⊢L ⊢L′) = ¬⊢M ⊢M′

¬switch : ∀ {Γ M A B}
  → Γ ⊢ M ↑ A
  → A ≢ B
    ---------------
  → ¬ Γ ⊢ (M ↑) ↓ B
¬switch ⊢M A≢B (⊢↑ ⊢M′ A′≡B) rewrite uniq-↑ ⊢M ⊢M′ = A≢B A′≡B

ext∋ : ∀ {Γ B x y}
  → x ≢ y
  → ¬ ∃[ A ]( Γ ∋ x ⦂ A )
    -----------------------------
  → ¬ ∃[ A ]( Γ , y ⦂ B ∋ x ⦂ A )
ext∋ x≢y _  ⟨ A , Z ⟩       =  x≢y refl
ext∋ _   ¬∃ ⟨ A , S _ ∋x ⟩  =  ¬∃ ⟨ A , ∋x ⟩

lookup : ∀ (Γ : Context) (x : Id)
    -----------------------
  → Dec (∃[ A ](Γ ∋ x ⦂ A))
lookup ∅ x                        =  no  (λ ())
lookup (Γ , y ⦂ B) x with x ≟ y
... | yes refl                    =  yes ⟨ B , Z ⟩
... | no x≢y with lookup Γ x
...             | no  ¬∃          =  no  (ext∋ x≢y ¬∃)
...             | yes ⟨ A , ∋x ⟩  =  yes ⟨ A , S x≢y ∋x ⟩

synthesize : ∀ (Γ : Context) (M : Term⁺)
    -----------------------
  → Dec (∃[ A ](Γ ⊢ M ↑ A))

inherit : ∀ (Γ : Context) (M : Term⁻) (A : Type)
    ---------------
  → Dec (Γ ⊢ M ↓ A)

synthesize Γ (` x) with lookup Γ x
... | no  ¬∃              =  no  (λ{ ⟨ A , ⊢` ∋x ⟩ → ¬∃ ⟨ A , ∋x ⟩ })
... | yes ⟨ A , ∋x ⟩      =  yes ⟨ A , ⊢` ∋x ⟩
synthesize Γ (L · M) with synthesize Γ L
... | no  ¬∃              =  no  (λ{ ⟨ _ , ⊢L  · _  ⟩  →  ¬∃ ⟨ _ , ⊢L ⟩ })
... | yes ⟨ o ,    ⊢L ⟩  =  no  (λ{ ⟨ _ , ⊢L′ · _  ⟩  →  o≢⇒ (uniq-↑ ⊢L ⊢L′) })
... | yes ⟨ A ⇒ B , ⊢L ⟩ with inherit Γ M A
...    | no  ¬⊢M          =  no  (¬arg ⊢L ¬⊢M)
...    | yes ⊢M           =  yes ⟨ B , ⊢L · ⊢M ⟩
synthesize Γ (M ↓ A) with inherit Γ M A
... | no  ¬⊢M             =  no  (λ{ ⟨ _ , ⊢↓ ⊢M ⟩  →  ¬⊢M ⊢M })
... | yes ⊢M              =  yes ⟨ A , ⊢↓ ⊢M ⟩

inherit Γ (ƛ x ⇒ N) o      =  no  (λ())
inherit Γ (ƛ x ⇒ N) (A ⇒ B) with inherit (Γ , x ⦂ A) N B
... | no ¬⊢N                =  no  (λ{ (⊢ƛ ⊢N)  →  ¬⊢N ⊢N })
... | yes ⊢N                =  yes (⊢ƛ ⊢N)
inherit Γ (M ↑) B with synthesize Γ M
... | no  ¬∃                =  no  (λ{ (⊢↑ ⊢M _) → ¬∃ ⟨ _ , ⊢M ⟩ })
... | yes ⟨ A , ⊢M ⟩ with A ≟Tp B
...   | no  A≢B             =  no  (¬switch ⊢M A≢B)
...   | yes A≡B             =  yes (⊢↑ ⊢M A≡B)

---------------------------------------------------------------------------------
-- Church numerals

CNat : Type
CNat = (o ⇒ o) ⇒ o ⇒ o

zero : Term⁻
zero = (ƛ "f" ⇒ ƛ "x" ⇒ (` "x") ↑ )

one : Term⁻
one = (ƛ "f" ⇒ ƛ "x" ⇒ ` "f" · (` "x" ↑) ↑)

two : Term⁻
two = (ƛ "f" ⇒ ƛ "x" ⇒ ` "f" · (` "f" · (` "x" ↑) ↑) ↑)

⊢zero : ∅ ⊢ zero ↓ CNat
⊢zero  = ⊢ƛ (⊢ƛ (⊢↑ (⊢` Z) refl))

⊢one : ∅ ⊢ one ↓ CNat
⊢one  = ⊢ƛ (⊢ƛ (⊢↑ (⊢` (S ("f" ≠ "x") Z) · ⊢↑ (⊢` Z) refl) refl))

⊢two : ∅ ⊢ two ↓ CNat
⊢two = ⊢ƛ (⊢ƛ (⊢↑ ((⊢` (S ("f" ≠ "x") Z)) · ⊢↑ (⊢` (S ("f" ≠ "x") Z) · ⊢↑ (⊢` Z) refl) refl) refl))

succ : Term⁻
succ = ƛ "n" ⇒ (ƛ "f" ⇒ ƛ "x" ⇒ ` "f" · (` "n" · (` "f" ↑) · (` "x" ↑) ↑) ↑)

sZero : Term⁻
sZero = ((succ ↓ CNat ⇒ CNat) · zero) ↑

sOne : Term⁻
sOne = ((succ ↓ CNat ⇒ CNat) · (((succ ↓ CNat ⇒ CNat) · zero) ↑)) ↑

⊢succ : ∅ ⊢ succ ↓ CNat ⇒ CNat
⊢succ =
  ⊢ƛ (⊢ƛ (⊢ƛ (⊢↑ ((⊢` (S ("f" ≠ "x") Z))
    · ⊢↑ (((⊢` (S ("n" ≠ "x") (S ("n" ≠ "f") Z)))
      · ⊢↑ (⊢` (S ("f" ≠ "x") Z)) refl) · ⊢↑ (⊢` Z) refl) refl) refl)))

⊢sZero : ∅ ⊢ sZero ↓ CNat
⊢sZero = ⊢↑ (⊢↓ ⊢succ · ⊢zero) refl

⊢sOne : ∅ ⊢ sOne ↓ CNat
⊢sOne = ⊢↑ (⊢↓ ⊢succ · ⊢sZero) refl

--------------------------------------------------------------------------------
-- Applies n times `succ`.
appS : ℕ → Term⁻ → Term⁻
appS zℕ    M = M
appS (sℕ n) M = appS n (((succ ↓ CNat ⇒ CNat) · M) ↑)

sZero₁ : Term⁻
sZero₁ = appS 1 zero

sOne₁ : Term⁻
sOne₁ = appS 2 zero

⊢sZero₁ : ∅ ⊢ sZero₁ ↓ CNat
⊢sZero₁ = ⊢↑ (⊢↓ ⊢succ · ⊢zero) refl

⊢sOne₁ : ∅ ⊢ sOne₁ ↓ CNat
⊢sOne₁ = ⊢↑ (⊢↓ ⊢succ · ⊢↑ (⊢↓ ⊢succ · ⊢zero) refl) refl

--------------------------------------------------------------------------------

cN : ℕ → Term⁻
cN zℕ     = zero
cN (sℕ n) = ((succ ↓ CNat ⇒ CNat) · cN n) ↑

⊢cN : (n : ℕ) → ∅ ⊢ cN n ↓ CNat
⊢cN zℕ     = ⊢zero
⊢cN (sℕ n) = ⊢↑ (⊢↓ ⊢succ · ⊢cN n) refl

--------------------------------------------------------------------------------

_ : inherit ∅ zero CNat ≡ yes ⊢zero
_ = refl

_ : inherit ∅ one CNat ≡ yes ⊢one
_ = refl
