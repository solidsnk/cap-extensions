module Op.DirectCapEx.FA where

open import Data.Nat
open import Data.List hiding (lookup)
open import Data.List.Any
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.List.All hiding (lookup)
open import Data.Bool
open import Data.Maybe
open import Data.Unit

open import Op.SourceSyntax
open import Op.SourceSemantics as S
open import Op.DirectCapEx as C
open import Op.DirectCapEx.Properties
open import Op.DirectCapEx.Bisim

-- Reflexive, transitive bisimulation
cmdSim→* : ∀ {X : Exports} {P : Prog X} {L₁ L₂ : StoreTy}
           {S₁ : State X L₁} {S₂ : State X L₂} {C₁ : CapState X L₁} →
           S₁ ∼ C₁ →  P ⊨ S₁ ⟶* S₂ → ∃ λ C₂ → (S₂ ∼ C₂ × P ⊩ C₁ ⟶* C₂)
cmdSim→* {C₁ = C₁} rel done = C₁ , rel , done
cmdSim→* rel (step x ev) with cmdSim→ rel x
cmdSim→* rel (step x ev) | stateS , relS , evS with cmdSim→* relS ev
cmdSim→* rel (step x ev) | stateS , relS , evS | stateR , relR , evR = stateR , relR , step evS evR

cmdSim←* : ∀ {X : Exports} {P : Prog X} {L₁ L₂ : StoreTy}
           {S₁ : State X L₁} {C₁ : CapState X L₁} {C₂ : CapState X L₂} →
           S₁ ∼ C₁ → P ⊩ C₁ ⟶* C₂ → ∃ λ S₂ → (S₂ ∼ C₂ × P ⊨ S₁ ⟶* S₂)
cmdSim←* {S₁ = S₁} rel done = S₁ , rel , done
cmdSim←* rel (step x ev) with cmdSim← rel x
cmdSim←* rel (step x ev) | stateS , relS , evS with cmdSim←* relS ev
cmdSim←* rel (step x ev) | stateS , relS , evS | stateR , relR , evR = stateR , relR , step evS evR

FAP→ : ∀ {d} {m} {X} {f₁ f₂ : FunDef (d ∷ m ∷ X)} {i₁ i₂} →
       S.ctx→ f₁ f₂ i₁ i₂ → C.ctx→ f₁ f₂ i₁ i₂
FAP→ s≡ ctx term with cmdSim←* ((undef , undef) ∷ [] , nn ∷ []) term
FAP→ s≡ ctx term | ([] ↓ [] ↓ []) , relSt , evH₁ with cmdSim→* ((undef , undef) ∷ [] , (nn ∷ [])) (s≡ ctx evH₁)
FAP→ s≡ ctx term | ([] ↓ [] ↓ []) , relSt , evH₁ | ([] ⅋ [] ⅋ []) , relC , evL₂ = evL₂

FAP← : ∀ {d} {m} {X} {f₁ f₂ : FunDef (d ∷ m ∷ X)} {i₁ i₂} →
       C.ctx→ f₁ f₂ i₁ i₂ → S.ctx→ f₁ f₂ i₁ i₂
FAP← c≡ ctx term with cmdSim→* ((undef , undef) ∷ [] , nn ∷ []) term
FAP← c≡ ctx term | ([] ⅋ [] ⅋ []) , relC , evL₁ with cmdSim←* ((undef , undef) ∷ [] , (nn ∷ [])) (c≡ ctx evL₁)
FAP← c≡ ctx term | ([] ⅋ [] ⅋ []) , relC , evL₁ | ([] ↓ [] ↓ []) , relSt , evH₂ = evH₂

-- Full abstraction
FA→ : ∀ {d} {m} {X} {f₁ f₂ : FunDef (d ∷ m ∷ X)} {i₁ i₂} →
      S.≡-ctx f₁ f₂ i₁ i₂ → C.≡-ctx f₁ f₂ i₁ i₂
FA← : ∀ {d} {m} {X} {f₁ f₂ : FunDef (d ∷ m ∷ X)} {i₁ i₂} →
      C.≡-ctx f₁ f₂ i₁ i₂ → S.≡-ctx f₁ f₂ i₁ i₂
FA→ (fst , snd) = (FAP→ fst) , (FAP→ snd)
FA← (fst , snd) = (FAP← fst) , (FAP← snd)
