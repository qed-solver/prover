module Normal where

open import Agda.Primitive renaming (Set to Type)
open import Data.Nat
open import Data.List

open import Shared
import Syntax
import Partial

record Term (Γ : Ctx) : Type₁

UExp : Ctx → Type₁
UExp Γ = List (Term Γ)

Rel = Lam UExp

Exp = Expr Rel
Exps = Exprs Rel

Hd = Head Rel
App = Appl Rel

Log : Ctx → Type₁
data LRel (Γ S : Ctx) : Type₁ where
  lam : Lam Log Γ S → LRel Γ S
Log = Logi Rel LRel

record Term Γ where
  inductive
  constructor _⊢_⊗_
  field
    Scope : Ctx
    logic : Log (Γ ++ Scope)
    apps : List (App (Γ ++ Scope))
