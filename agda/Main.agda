module Main where

open import Agda.Primitive renaming (Set to Type)
open import Data.List
open import Data.Product hiding (∃; map)
open import Data.Unit.Polymorphic renaming (tt to ⊤-tt)
open import Algebra.Bundles

open import Shared
import Syntax
import Partial
import Normal
import Stable

open Eval ⦃ ... ⦄
open Shared.Expr
open Shared.Head
open Shared.Logi

instance
  open RawSemiring ⦃ ... ⦄
  open Syntax.UExp
  open Syntax.Rel
  open Partial

  {-# TERMINATING #-}
  syn⇒par-rel : ∀ {Γ Δ S} → Eval (Partial.Exps Δ Γ) (Syntax.Rel Γ S) (Partial.Rel Δ S)
  syn⇒par-rel .eval env (var x) = var x
  syn⇒par-rel .eval env (hop name args rel) = hop name (eval env args) (eval env rel)
  syn⇒par-rel .eval env (lam (ƛ f)) = clos (env ⦊ f)

  syn⇒par-log : ∀ {Γ Δ} → Eval (Partial.Exps Δ Γ) (Syntax.UExp Γ) (Partial.Log Δ)
  syn⇒par-log .eval env 𝟘 = ff
  syn⇒par-log .eval env 𝟙 = tt
  syn⇒par-log .eval env (e₁ ⊕ e₂) = eval env e₁ ∨ eval env e₂
  syn⇒par-log .eval env (e₁ ⊗ e₂) = eval env e₁ ∧ eval env e₂
  syn⇒par-log .eval env ∥ e ∥ = eval env e
  syn⇒par-log .eval env (¬ e) = ¬ (eval env e)
  syn⇒par-log .eval env (∑ e) = ∃ (env ⦊ e)
  syn⇒par-log .eval env ⟦ x ⟧ = ⟦ eval env x ⟧
  syn⇒par-log .eval env (var x ∘ args) = neu (var x ∘ eval env args)
  syn⇒par-log .eval env (hop name h-args rel ∘ args) =
    neu (hop name (eval env h-args) (eval env rel) ∘ (eval env args))
  syn⇒par-log .eval env (lam (ƛ f) ∘ args) = eval (concat-exps env (eval env args)) f

  syn⇒par-uexp : ∀ {Γ Δ} → Eval (Partial.Exps Δ Γ) (Syntax.UExp Γ) (Partial.UExp Δ)
  syn⇒par-uexp .eval env 𝟘 = 0#
  syn⇒par-uexp .eval env 𝟙 = 1#
  syn⇒par-uexp .eval env (u₁ ⊕ u₂) = eval env u₁ + eval env u₂
  syn⇒par-uexp .eval env (u₁ ⊗ u₂) = eval env u₁ * eval env u₂
  syn⇒par-uexp .eval env ∥ u ∥ = [ log-uexp (eval env u) ]
  syn⇒par-uexp .eval env (¬ u) = [ log-uexp (¬ (eval env u)) ]
  syn⇒par-uexp .eval env (∑ u) = [ sum-uexp (clos (env ⦊ u)) ]
  syn⇒par-uexp .eval env ⟦ x ⟧ = [ log-uexp ⟦ eval env x ⟧ ]
  syn⇒par-uexp .eval env (var x ∘ args) =  [ app-uexp (var x ∘ (eval env args)) ]
  syn⇒par-uexp .eval env (hop name h-args rel ∘ args) =
    [ app-uexp (hop name (eval env h-args) (eval env rel) ∘ (eval env args)) ]
  syn⇒par-uexp .eval env (lam (ƛ f) ∘ args) = eval (concat-exps env (eval env args)) f

instance
  open Normal
  open Lift ⦃ ... ⦄
  open RawMonoid ⦃ ... ⦄
  open import Relation.Binary.PropositionalEquality hiding ([_])
  open import Data.List.Properties

  par⇒nom-rel : ∀ {Γ S} → Eval ⊤ (Partial.Rel Γ S) (Normal.Rel Γ S)
  par⇒nom-uexp : ∀ {Γ} → Eval ⊤ (Partial.UExp Γ) (Normal.UExp Γ)

  par⇒nom-rel {Γ} {S} .eval env (var x) = ƛ [ [] ⊢ tt ⊗ [ app ] ]
    where
    app = subst Normal.App (sym (++-identityʳ _)) (var x ∘ vars Γ S)
  par⇒nom-rel {Γ} {S} .eval env (hop name args rel) = ƛ [ [] ⊢ tt ⊗ [ app ] ]
    where
    args' = eval env (↑ S args)
    rel' = eval env (↑ S rel)
    app = subst Normal.App (sym (++-identityʳ _)) (hop name args' rel' ∘ vars Γ S)
  par⇒nom-rel {Γ} {S} .eval e (clos (env ⦊ body)) =
    ƛ (eval e (eval (concat-exps (↑ S env) (vars Γ S)) body))

  par⇒nom-lrel : ∀ {Γ S} → Eval ⊤ (Partial.LRel Γ S) (Normal.LRel Γ S)
  par⇒nom-lrel {Γ} {S} .eval e (env ⦊ body) =
    lam (ƛ (eval e (eval (concat-exps (↑ S env) (vars Γ S)) body)))

  {-# TERMINATING #-}
  par⇒nom-term : ∀ {Γ} → Eval ⊤ (Partial.Term Γ) (Normal.UExp Γ)
  par⇒nom-term .eval env (logic ⊗ apps ⊗ []) =
    let logic = subst Normal.Log (sym (++-identityʳ _)) (eval env logic)
        apps = map (λ app → subst Normal.App (sym (++-identityʳ _)) (eval env app)) apps
    in [ [] ⊢ logic ⊗ apps ]
  par⇒nom-term .eval env (logic ⊗ apps ⊗ ((S , sum) ∷ sums)) =
    concatMap (λ t → (wrap S (eval env (t ∙ ↑ S (logic ⊗ apps ⊗ sums))))) (unwrap sum)
    where
    unwrap : ∀ {Γ S} → Partial.Rel Γ S → Partial.UExp (Γ ++ S)
    unwrap {Γ} {S} (var x) = [ tt ⊗ [ (var x) ∘ (vars Γ S) ] ⊗ [] ]
    unwrap {Γ} {S} (hop name args rel) =
      [ tt ⊗ [ hop name (↑ S args) (↑ S rel) ∘ (vars Γ S) ] ⊗ [] ]
    unwrap {Γ} {S} (clos (env ⦊ body)) = eval (concat-exps (↑ S env) (vars Γ S)) body
    wrap : ∀ {Γ} S → Normal.UExp (Γ ++ S) → Normal.UExp Γ
    wrap S uexp = map wrap-term uexp
      where
      wrap-term : ∀ {Γ S} → Normal.Term (Γ ++ S) → Normal.Term Γ
      wrap-term {Γ} {S} (Scope ⊢ logic ⊗ apps) =
        let logic = subst Normal.Log (++-assoc Γ _ _) logic
            apps = map (subst Normal.App (++-assoc Γ _ _)) apps
        in (S ++ Scope) ⊢ logic ⊗ apps
  par⇒nom-uexp .eval env u = concatMap (eval env) u

postulate min-rep : ∀ {Γ Δ} S → Normal.Log (Γ ++ S) → Stable.Exps Δ Γ → Σ[ S' ∈ Ctx ] Stable.Exps (Δ ++ S') S

instance
  open Stable
  {-# TERMINATING #-}
  nom⇒stb-rel : ∀ {Γ Δ S} → Eval (Stable.Exps Δ Γ) (Normal.Rel Γ S) (Stable.Rel Δ S)
  nom⇒stb-rel .eval env (ƛ f) = clos (env ⦊ f)

  nom⇒stb-lrel : ∀ {Γ Δ S} → Eval (Stable.Exps Δ Γ) (Normal.LRel Γ S) (Stable.LRel Δ S)
  nom⇒stb-lrel .eval env (lam (ƛ body)) = env ⦊ body

  nom⇒stb-term : ∀ {Γ Δ} → Eval (Stable.Exps Δ Γ) (Normal.Term Γ) (Stable.Term Δ)
  nom⇒stb-term .eval env (Scope ⊢ logic ⊗ apps) =
    let S' , reps = min-rep Scope logic env
        env = concat-exps (↑ S' env) reps
    in S' ⊢ eval env logic ⊗ map (eval env) apps
  nom⇒stb-uexp : ∀ {Γ Δ} → Eval (Stable.Exps Δ Γ) (Normal.UExp Γ) (Stable.UExp Δ)
  nom⇒stb-uexp .eval env u = map (eval env) u

instance
  {-# TERMINATING #-}
  stb⇒nom-rel : ∀ {Γ S} → Eval ⊤ (Stable.Rel Γ S) (Normal.Rel Γ S)
  stb⇒nom-uexp : ∀ {Γ} → Eval ⊤ (Stable.UExp Γ) (Normal.UExp Γ)
  stb⇒nom-rel {Γ} {S} .eval e (clos (env ⦊ body)) =
    ƛ (eval e (eval (concat-exps (↑ S env) (vars Γ S)) body))

  stb⇒nom-lrel : ∀ {Γ S} → Eval ⊤ (Stable.LRel Γ S) (Normal.LRel Γ S)
  stb⇒nom-lrel {Γ} {S} .eval e (env ⦊ body) = lam (ƛ (eval e body'))
    where
    body' : Stable.Log (Γ ++ S)
    body' = eval (concat-exps (↑ S env) (vars Γ S)) body

  stb⇒nom-term : ∀ {Γ} → Eval ⊤ (Stable.Term Γ) (Normal.Term Γ)
  stb⇒nom-term .eval env (Scope ⊢ logic ⊗ apps) =
    Scope ⊢ eval env logic ⊗ map (eval env) apps

  stb⇒nom-uexp .eval env u = map (eval env) u

evaluate : ∀ {S} → Syntax.Rel [] S → Normal.Rel [] S
evaluate {S} syn = eval _ stb
  where
  par : Partial.Rel [] S
  par = eval [] syn
  nom = eval _ par
  stb = eval [] nom
