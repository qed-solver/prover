module Stable where

open import Agda.Primitive renaming (Set to Type)
open import Data.Nat
open import Data.List

open import Shared
import Normal

data Rel (Γ S : Ctx) : Type₁
record Term (Γ : Ctx) : Type₁

Exp = Expr Rel
Exps = Exprs Rel

UExp : Ctx → Type₁
UExp Γ = List (Term Γ)

data Rel Γ S where
  var : ℕ → Rel Γ S
  hop : ∀ {A} → ℕ → Exps Γ A → Rel Γ S → Rel Γ S
  _⦊_ : ∀ {Γ'} → Exps Γ Γ' → Normal.UExp (Γ' ++ S) → Rel Γ S

Hd = Head Rel
App = Appl Rel
Log = Logi Rel

record Term Γ where
  inductive
  constructor _⊢_⊗_
  field
    Scope : Ctx
    logic : Log (Γ ++ Scope)
    apps : List (App (Γ ++ Scope))

instance
  open Lift ⦃ ... ⦄
  open Term
  open Rel
  {-# TERMINATING #-}
  rel-lift : ∀ {S} → Lift (λ Γ → Rel Γ S)
  rel-lift .↑ Δ (var x) = var x
  rel-lift .↑ Δ (hop name args rel) = hop name (↑ Δ args) (↑ Δ rel)
  rel-lift .↑ Δ (env ⦊ body) = ↑ Δ env ⦊ body
