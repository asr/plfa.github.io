import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (Dec; yes; no)
open import TakeDropDec2



