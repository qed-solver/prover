module Partial where

open import Agda.Primitive renaming (Set to Type)
open import Agda.Builtin.Equality
open import Algebra.Bundles
open import Data.Product hiding (∃; map)
open import Data.Bool hiding (_∧_; _∨_)
open import Data.List hiding (head)
open import Data.Fin hiding (_+_)
open import Data.Nat hiding (_+_; _*_)

open import Shared
import Syntax

data Rel (Γ S : Ctx) : Type₁

Exp = Expr Rel
Exps = Exprs Rel

data Rel Γ S where
  var : ℕ → Rel Γ S
  hop : ∀ {A} → ℕ → Exps Γ A → Rel Γ S → Rel Γ S
  clos : Clos Rel Syntax.UExp Γ S → Rel Γ S

Rel' = λ Γ → Σ[ S ∈ Ctx ] Rel Γ S
Hd = Head Rel
App = Appl Rel
LRel = Clos Rel Syntax.UExp
Log = Logi Rel LRel

record Term (Γ : Ctx) : Type₁ where
  inductive
  constructor _⊗_⊗_
  field
    logic : Log Γ
    apps : List (App Γ)
    sums : List (Rel' Γ)

log-uexp : ∀ {Γ} → Log Γ → Term Γ
log-uexp log = log ⊗ [] ⊗ []

app-uexp : ∀ {Γ} → App Γ → Term Γ
app-uexp app = tt ⊗ [ app ] ⊗ []

sum-uexp : ∀ {Γ S} → Rel Γ S → Term Γ
sum-uexp {S = S} sum = tt ⊗ [] ⊗ [ S , sum ]

UExp : Ctx → Type₁
UExp Γ = List (Term Γ)

instance
  open Lift ⦃ ... ⦄
  open Term
  open Rel
  open Clos
  uexp-lift : Lift UExp
  term-lift : Lift Term
  {-# TERMINATING #-}
  rel-lift : ∀ {S} → Lift (λ Γ → Rel Γ S)
  rel'-lift : Lift Rel'

  rel-lift .↑ Δ (var x) = var x
  rel-lift .↑ Δ (hop name args rel) = hop name (↑ Δ args) (↑ Δ rel)
  rel-lift .↑ Δ (clos (env ⦊ body)) = clos (↑ Δ env ⦊ body)

  uexp-lift .↑ {Γ} Δ uexp = map (↑ Δ) uexp

  term-lift .↑ Δ term .logic = ↑ Δ (term .logic)
  term-lift .↑ Δ term .apps = map (↑ Δ) (term .apps)
  term-lift .↑ Δ term .sums = map (↑ Δ) (term .sums)

  rel'-lift .↑ Δ (S , rel) = S , ↑ Δ rel

instance
  open RawMonoid ⦃ ... ⦄
  term-monoid : ∀ {Γ} → RawMonoid _ _
  term-monoid {Γ} .Carrier = Term Γ
  term-monoid ._≈_ = _≡_
  term-monoid ._∙_ (l₁ ⊗ as₁ ⊗ ss₁) (l₂ ⊗ as₂ ⊗ ss₂) =
    (l₁ ∧ l₂) ⊗ (as₁ ++ as₂) ⊗ (ss₁ ++ ss₂)
  term-monoid .ε = tt ⊗ [] ⊗ []

  open RawSemiring ⦃ ... ⦄
  uexp-semiring : ∀ {Γ} → RawSemiring _ _
  uexp-semiring {Γ} .Carrier = UExp Γ
  uexp-semiring ._≈_ = _≡_
  uexp-semiring ._+_ = _++_
  uexp-semiring ._*_ u = concatMap (λ t → map (_∙ t) u)
  uexp-semiring .0# = []
  uexp-semiring .1# = [ ε ]
