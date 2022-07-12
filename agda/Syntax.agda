module Syntax where

open import Agda.Primitive renaming (Set to Type)
open import Data.Bool
open import Data.List
open import Data.Nat

open import Shared

data UExp (Γ : Ctx) : Type₁
data Rel (Γ S : Ctx) : Type₁

Exp = Expr Rel
Exps = Exprs Rel

data UExp Γ where
  𝟘 : UExp Γ
  𝟙 : UExp Γ
  _⊕_ : UExp Γ → UExp Γ → UExp Γ
  _⊗_ : UExp Γ → UExp Γ → UExp Γ
  ∥_∥ : UExp Γ → UExp Γ
  ¬ : UExp Γ → UExp Γ
  ∑ : ∀ {S} → UExp (Γ ++ S) → UExp Γ
  ⟦_⟧ : Exp Γ Bool → UExp Γ
  _∘_ : ∀ {S} → Rel Γ S → Exps Γ S → UExp Γ

data Rel Γ S where
  var : ℕ → Rel Γ S
  hop : ∀ {A} → ℕ → Exprs Rel Γ A → Rel Γ S → Rel Γ S
  lam : Lam UExp Γ S → Rel Γ S
