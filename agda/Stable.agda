module Stable where

open import Agda.Primitive renaming (Set to Type)
open import Data.Nat
open import Data.List

open import Shared
import Normal

record Term (Γ : Ctx) : Type₁

data Rel (Γ S : Ctx) : Type₁ where
  clos : Clos Rel Normal.UExp Γ S → Rel Γ S

Exp = Expr Rel
Exps = Exprs Rel

UExp : Ctx → Type₁
UExp Γ = List (Term Γ)

Hd = Head Rel
App = Appl Rel
LRel = Clos Rel Normal.Log
Log = Logi Rel LRel

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
  rel-lift .↑ Δ (clos (env ⦊ body)) = clos (↑ Δ env ⦊ body)
