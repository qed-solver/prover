{-# OPTIONS --allow-unsolved-metas #-}
module Shared where

open import Agda.Primitive renaming (Set to Type)
open import Data.Bool hiding (_∧_; _∨_)
open import Data.Fin
open import Data.List hiding (head)
open import Data.Nat

Ctx = List Type

data Expr (R : Ctx → Ctx → Type₁) (Γ : Ctx) : Type → Type₁

data Exprs (R : Ctx → Ctx → Type₁) (Γ : Ctx) : Ctx → Type₁ where
  [] : Exprs R Γ []
  _∷_ : ∀ {T Δ} → Expr R Γ T → Exprs R Γ Δ → Exprs R Γ (T ∷ Δ)

data Expr R Γ where
  var : ∀ l → Expr R Γ (lookup Γ l)
  op : ∀ {T A} → ℕ → Exprs R Γ A → Expr R Γ T
  hop : ∀ {T S A} → ℕ → Exprs R Γ A → R Γ S → Expr R Γ T

record Lam (U : Ctx → Type₁) (Γ S : Ctx) : Type₁ where
  constructor ƛ
  field
    body : U (Γ ++ S)

data Clos (R : Ctx → Ctx → Type₁) (U : Ctx → Type₁) (Γ S : Ctx) : Type₁ where
  _⦊_ : ∀ {Γ'} → Exprs R Γ Γ' → U (Γ' ++ S) → Clos R U Γ S

data Head (R : Ctx → Ctx → Type₁) (Γ S : Ctx) : Type₁ where
  var : ℕ → Head R Γ S
  hop : ∀ {A} → ℕ → Exprs R Γ A → R Γ S → Head R Γ S

record Appl (R : Ctx → Ctx → Type₁) (Γ : Ctx) : Type₁ where
  constructor _∘_
  field
    {S} : Ctx
    head : Head R Γ S
    args : Exprs R Γ S

data Logi (R L : Ctx → Ctx → Type₁) (Γ : Ctx) : Type₁ where
  tt : Logi R L Γ
  ff : Logi R L Γ
  ¬ : Logi R L Γ → Logi R L Γ
  _∧_ : Logi R L Γ → Logi R L Γ → Logi R L Γ
  _∨_ : Logi R L Γ → Logi R L Γ → Logi R L Γ
  ⟦_⟧ : Expr R Γ Bool → Logi R L Γ
  neu : Appl R Γ → Logi R L Γ
  ∃ : ∀ {S} → L Γ S → Logi R L Γ

lookup-exps : ∀ {R Γ Δ} → Exprs R Γ Δ → ∀ l → Expr R Γ (lookup Δ l)
lookup-exps (e ∷ es) zero = e
lookup-exps (e ∷ es) (suc l) = lookup-exps es l

concat-exps : ∀ {R Γ Δ₁ Δ₂} → Exprs R Γ Δ₁ → Exprs R Γ Δ₂ → Exprs R Γ (Δ₁ ++ Δ₂)
concat-exps [] es = es
concat-exps (e ∷ es₁) es₂ = e ∷ concat-exps es₁ es₂

-- TODO: Define it!
postulate vars : ∀ {R} Γ S → Exprs R (Γ ++ S) S

record Lift (Tm : Ctx → Type₁) : Type₁ where
  field
    ↑ : ∀ {Γ} Δ → Tm Γ → Tm (Γ ++ Δ)

record Eval (E S T : Type₁) : Type₂ where
  field
    eval : E → S → T

instance
  open Lift ⦃ ... ⦄
  open import Relation.Binary.PropositionalEquality hiding ([_])
  open import Data.List.Properties
  -- Lifting should be essentially a no-op
  -- when using natural nubmers to represent de-Bruijn levels.
  expr-lift : ∀ {R B} → ⦃ ∀ {S} → Lift (λ Γ → R Γ S) ⦄ → Lift (λ Γ → Expr R Γ B)
  exprs-lift : ∀ {R S'} → ⦃ ∀ {S} → Lift (λ Γ → R Γ S) ⦄ → Lift (λ Γ → Exprs R Γ S')
  expr-lift {R} .↑ {Γ} Δ (var l) = subst (Expr R (Γ ++ Δ)) (eq-type Γ Δ l) (var (lift-lvl Γ Δ l))
    where
    lift-lvl : (Γ Δ : Ctx) → Fin (length Γ) → Fin (length (Γ ++ Δ))
    lift-lvl Γ Δ l = subst Fin (sym (length-++ Γ)) (inject+ {length Γ} (length Δ) l)
    -- TODO: Prove it!
    postulate eq-type : ∀ Γ Δ l → lookup (Γ ++ Δ) (lift-lvl Γ Δ l) ≡ lookup Γ l
  expr-lift .↑ Δ (op name args) = op name (↑ Δ args)
  expr-lift .↑ Δ (hop name args rel) = hop name (↑ Δ args) (↑ Δ rel)
  exprs-lift .↑ Δ [] = []
  exprs-lift .↑ Δ (e ∷ es) = ↑ Δ e ∷ ↑ Δ es

  head-lift : ∀ {R S'} → ⦃ ∀ {S} → Lift (λ Γ → R Γ S) ⦄ → Lift (λ Γ → Head R Γ S')
  head-lift .↑ Δ (var x) = var x
  head-lift .↑ Δ (hop name args rel) = hop name (↑ Δ args) (↑ Δ rel)

  appl-lift : ∀ {R} → ⦃ ∀ {S} → Lift (λ Γ → R Γ S) ⦄ → Lift (λ Γ → Appl R Γ)
  appl-lift .↑ Δ (head ∘ args) = ↑ Δ head ∘ ↑ Δ args

  {-# TERMINATING #-}
  clos-lift : ∀ {R U S} → ⦃ ∀ {S} → Lift (λ Γ → R Γ S) ⦄ → Lift (λ Γ → Clos R U Γ S)
  clos-lift .↑ Δ (env ⦊ body) = (↑ Δ env) ⦊ body

  logi-lift : ∀ {R L}
              → ⦃ ∀ {S} → Lift (λ Γ → R Γ S) ⦄
              → ⦃ ∀ {S} → Lift (λ Γ → L Γ S) ⦄
              → Lift (Logi R L)
  logi-lift .↑ Δ tt = tt
  logi-lift .↑ Δ ff = ff
  logi-lift .↑ Δ (¬ l) = ¬ (↑ Δ l)
  logi-lift .↑ Δ (l₁ ∧ l₂) = (↑ Δ l₁) ∧ (↑ Δ l₂)
  logi-lift .↑ Δ (l₁ ∨ l₂) = (↑ Δ l₁) ∨ (↑ Δ l₂)
  logi-lift .↑ Δ ⟦ b ⟧ = ⟦ ↑ Δ b ⟧
  logi-lift .↑ Δ (neu app) = neu (↑ Δ app)
  logi-lift .↑ Δ (∃ pred) = ∃ (↑ Δ pred)

instance
  open Eval ⦃ ... ⦄
  expr-eval : ∀ {Γ Δ R R' A}
              → ⦃ ∀ {S} → Eval (Exprs R' Δ Γ) (R Γ S) (R' Δ S) ⦄
              → Eval (Exprs R' Δ Γ) (Expr R Γ A) (Expr R' Δ A)
  exprs-eval : ∀ {Γ Δ R R' A}
               → ⦃ ∀ {S} → Eval (Exprs R' Δ Γ) (R Γ S) (R' Δ S) ⦄
               → Eval (Exprs R' Δ Γ) (Exprs R Γ A) (Exprs R' Δ A)
  expr-eval .eval env (var l) = lookup-exps env l
  expr-eval .eval env (op name args) = op name (eval env args)
  expr-eval .eval env (hop name args rel) = hop name (eval env args) (eval env rel)
  exprs-eval .eval env [] = []
  exprs-eval .eval env (e ∷ es) = eval env e ∷ eval env es

  head-eval : ∀ {Γ Δ R R' A}
              → ⦃ ∀ {S} → Eval (Exprs R' Δ Γ) (R Γ S) (R' Δ S) ⦄
              → Eval (Exprs R' Δ Γ) (Head R Γ A) (Head R' Δ A)
  head-eval .eval env (var x) = var x
  head-eval .eval env (hop name args rel) = hop name (eval env args) (eval env rel)

  appl-eval : ∀ {Γ Δ R R'}
              → ⦃ ∀ {S} → Eval (Exprs R' Δ Γ) (R Γ S) (R' Δ S) ⦄
              → Eval (Exprs R' Δ Γ) (Appl R Γ) (Appl R' Δ)
  appl-eval .eval env (head ∘ args) = eval env head ∘ eval env args

  logi-eval : ∀ {Γ Δ R R' L L'}
              → ⦃ ∀ {S} → Eval (Exprs R' Δ Γ) (R Γ S) (R' Δ S) ⦄
              → ⦃ ∀ {S} → Eval (Exprs R' Δ Γ) (L Γ S) (L' Δ S) ⦄
              → Eval (Exprs R' Δ Γ) (Logi R L Γ) (Logi R' L' Δ)
  logi-eval .eval env tt = tt
  logi-eval .eval env ff = ff
  logi-eval .eval env (¬ l) = ¬ (eval env l)
  logi-eval .eval env (l₁ ∧ l₂) = eval env l₁ ∧ eval env l₂
  logi-eval .eval env (l₁ ∨ l₂) = eval env l₁ ∨ eval env l₂
  logi-eval .eval env ⟦ b ⟧ = ⟦ eval env b ⟧
  logi-eval .eval env (neu app) = neu (eval env app)
  logi-eval .eval env (∃ pred) = ∃ (eval env pred)

instance
  open import Data.Unit.Polymorphic using (⊤)
  expr-read : ∀ {Γ R R' A} → ⦃ ∀ {S} → Eval ⊤ (R Γ S) (R' Γ S) ⦄ → Eval ⊤ (Expr R Γ A) (Expr R' Γ A)
  exprs-read : ∀ {Γ R R' A} → ⦃ ∀ {S} → Eval ⊤ (R Γ S) (R' Γ S) ⦄ → Eval ⊤ (Exprs R Γ A) (Exprs R' Γ A)
  expr-read .eval env (var l) = var l
  expr-read .eval env (op name args) = op name (eval env args)
  expr-read .eval env (hop name args rel) = hop name (eval env args) (eval env rel)
  exprs-read .eval env [] = []
  exprs-read .eval env (e ∷ es) = eval env e ∷ eval env es

  head-read : ∀ {Γ R R' A} → ⦃ ∀ {S} → Eval ⊤ (R Γ S) (R' Γ S) ⦄ → Eval ⊤ (Head R Γ A) (Head R' Γ A)
  head-read .eval env (var x) = var x
  head-read .eval env (hop name args rel) = hop name (eval env args) (eval env rel)

  appl-read : ∀ {Γ R R'} → ⦃ ∀ {S} → Eval ⊤ (R Γ S) (R' Γ S) ⦄ → Eval ⊤ (Appl R Γ) (Appl R' Γ)
  appl-read .eval env (head ∘ args) = eval env head ∘ eval env args

  logi-read : ∀ {Γ R R' L L'}
              → ⦃ ∀ {S} → Eval ⊤ (R Γ S) (R' Γ S) ⦄
              → ⦃ ∀ {S} → Eval ⊤ (L Γ S) (L' Γ S) ⦄
              → Eval ⊤ (Logi R L Γ) (Logi R' L' Γ)
  logi-read .eval env tt = tt
  logi-read .eval env ff = ff
  logi-read .eval env (¬ l) = ¬ (eval env l)
  logi-read .eval env (l₁ ∧ l₂) = eval env l₁ ∧ eval env l₂
  logi-read .eval env (l₁ ∨ l₂) = eval env l₁ ∨ eval env l₂
  logi-read .eval env ⟦ b ⟧ = ⟦ eval env b ⟧
  logi-read .eval env (neu app) = neu (eval env app)
  logi-read .eval env (∃ rel) = ∃ (eval env rel)
