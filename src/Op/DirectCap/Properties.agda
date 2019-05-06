module Op.DirectCap.Properties where

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

open import Op.SourceSyntax
open import Op.SourceSemantics as S
open import Op.DirectCap as C

data +M {A B : Set} (P : A → B → Set) : Maybe A → Maybe B → Set where
  nn : +M P nothing nothing
  jj : ∀ {a} {b} → P a b → +M P (just a) (just b)

data _⇌_ {L : StoreTy} : Loc L → Addr → Set where
  rfl : ∀ {n} {n< : n <′ length L} {b} → (n ⋆ n< of b) ⇌ (n of b)

data _|⇌|_ : {L : StoreTy} → Ret L → Cret L → Set where
  [] : [] |⇌| []
  _∷_ : ∀ {L : StoreTy} {Γ : Ns} {R : Ret L} {C : Cret L} {l : Maybe (Loc L)} {a : Maybe Addr}
        → (+M _⇌_ ) l a → R |⇌| C → (_∷_ {Γ = Γ} l R) |⇌| (a ∷ C)

data _↝_ {L : StoreTy} : Val L → Cval → Set where
  unit : unit ↝ unit
  nat : ∀ {n} → nat n ↝ nat n
  poi : ∀ {n} {n< : n <′ length L} {b} → loc (n ⋆ n< of b) ↝ cap (n of b)
  undef : undef ↝ undef

CelRel : ∀ {L : StoreTy} → Pair L → Cell → Set
CelRel (a₁ -  v₁) (a₂ - v₂) = (a₁ ↝ a₂) × (v₁ ↝ v₂)

data _|↝|_ : {L : StoreTy} → Store L → Memory L → Set where
  [] : [] |↝| []
  _∷_ : ∀ {L : StoreTy} {Γ} {S : Store L} {M : Memory L}
        → {p : Pair (Γ ∷ L)} {c : Cell} → CelRel p c
        → S |↝| M → (p ∷ S) |↝| (c ∷ M)

data _∼_ {L : StoreTy} {X} : State X L → CapState X L → Set where
  _,_ : ∀ {C} {S : Store L} {M : Memory L} {R : Ret L} {Cr : Cret L} → S |↝| M → R |⇌| Cr
        → (S ↓ C ↓ R) ∼ (M ⅋ C ⅋ Cr)

leq : ∀ {m n} → (m< : m ≤′ n) → (m<' : m ≤′ n) → m< ≡ m<'
leq ≤′-refl ≤′-refl = refl
leq ≤′-refl (≤′-step m<') = ⊥-elim (≤-contra ≤′-refl m<')
leq (≤′-step m<) ≤′-refl = ⊥-elim (≤-contra ≤′-refl m<)
leq (≤′-step m<) (≤′-step m<') = cong ≤′-step (leq m< m<')

wk↝ : ∀ {L : StoreTy} {Γ} {v : Val L} {c : Cval} → v ↝ c → wkVal v Γ ↝ c
wk↝ unit = unit
wk↝ nat = nat
wk↝ poi = poi
wk↝ undef = undef

getRel→ : ∀ {L : StoreTy} {S : Store L} {M : Memory L}
          → S |↝| M → (l : Loc L)
          → S.get S l ↝ C.get ((Loc.base l) of (Loc.off l)) M (Loc.proof l)
getRel→ [] (base ⋆ () of off)
getRel→ (_∷_ {L} (fst , snd) mrel) (.(foldr (λ _ → suc) 0 L) ⋆ ≤′-refl of false) = fst
getRel→ (_∷_ {L} (fst , snd) mrel) (.(foldr (λ _ → suc) 0 L) ⋆ ≤′-refl of true) = snd
getRel→ (_∷_ {L} x mrel) (base ⋆ ≤′-step proof of off) = wk↝ (getRel→ mrel (base ⋆ proof of off))

-- Highlighting fail if not case splitting in off for last two lines
getRel← : ∀ {L : StoreTy} {S : Store L} {M : Memory L}
          → S |↝| M → (a : Addr) → (a∈M : a |∈| M)
          → S.get S (Addr.base a ⋆ a∈M of Addr.off a) ↝ C.get a M a∈M
getRel← [] a ()
getRel← (_∷_ {L} (fst , snd) mrel) (.(foldr (λ _ → suc) 0 L) of false) ≤′-refl = fst
getRel← (_∷_ {L} (fst , snd) mrel) (.(foldr (λ _ → suc) 0 L) of true) ≤′-refl = snd
getRel← (_∷_ {L} {S} x mrel) (base of false) (≤′-step a∈M) = wk↝ (getRel← mrel (base of false) a∈M)
getRel← (_∷_ {L} {S} x mrel) (base of true) (≤′-step a∈M) = wk↝ (getRel← mrel (base of true) a∈M)

↝≡ : ∀ {L : StoreTy} {v₁ v₂ : Val L} {c : Cval} → v₁ ↝ c → v₂ ↝ c → v₁ ≡ v₂
↝≡ unit unit = refl
↝≡ nat nat = refl
↝≡ (poi {n< = n<₁}) (poi {n< = n<}) rewrite leq n< n<₁ = refl
↝≡ undef undef = refl

≡↝ : ∀ {L : StoreTy} {v : Val L} {c₁ c₂ : Cval} → v ↝ c₁ → v ↝ c₂ → c₁ ≡ c₂
≡↝ unit unit = refl
≡↝ nat nat = refl
≡↝ poi poi = refl
≡↝ undef undef = refl

exprSim→ : ∀ {t} {L : StoreTy} {Γ : Ns} {S : Store (Γ ∷ L)}
             (e : Expr Γ t) {v : Val (Γ ∷ L)} {cv : Cval} {M : Memory (Γ ∷ L)}
           → S |↝| M → v ↝ cv → S ⊨ e ⇒ v → M ⊩ e ⇒ cv
exprSim→ (nat x) mrel nat nat> = nat>
exprSim→ unit mrel unit unit> = unit>
exprSim→ (bOp x l r) mrel nat (bOp> evl evr)
  = bOp> (exprSim→ l mrel nat evl) (exprSim→ r mrel nat evr)
exprSim→ (var (inj₁ refl)) ((unit , snd) ∷ mrel) unit var> = var>
exprSim→ (var (inj₁ refl)) ((nat , snd) ∷ mrel) nat var> = var>
exprSim→ (var (inj₁ refl)) ((poi , snd) ∷ mrel) poi var> = var>
exprSim→ (var (inj₁ refl)) ((undef , snd) ∷ mrel) undef var> = var>
exprSim→ (var (inj₂ refl)) ((fst , unit) ∷ mrel) unit var> = var>
exprSim→ (var (inj₂ refl)) ((fst , nat) ∷ mrel) nat var> = var>
exprSim→ (var (inj₂ refl)) ((fst , poi) ∷ mrel) poi var> = var>
exprSim→ (var (inj₂ refl)) ((fst , undef) ∷ mrel) undef var> = var>
exprSim→ (& x) mrel poi &> = &>
exprSim→ (* e) mrel vrel (*> {n = n} {n< = n<} {b} ev)
  rewrite ≡↝ vrel (getRel→ mrel (n ⋆ n< of b)) = C.*> (exprSim→ e mrel poi ev) n<

exprSim← : ∀ {t} {L : StoreTy} {Γ : Ns} {S : Store (Γ ∷ L)}
           (e : Expr Γ t) {v : Val (Γ ∷ L)} {cv : Cval} {M : Memory (Γ ∷ L)}
           → S |↝| M → v ↝ cv → M ⊩ e ⇒ cv → S ⊨ e ⇒ v
exprSim← (nat x) mrel nat nat> = nat>
exprSim← unit mrel unit unit> = unit>
exprSim← (bOp x l r) mrel nat (bOp> evl evr)
  = bOp> (exprSim← l mrel nat evl) (exprSim← r mrel nat evr)
exprSim← (var (inj₁ refl)) ((unit , snd) ∷ mrel) unit var> = var>
exprSim← (var (inj₁ refl)) ((nat , snd) ∷ mrel) nat var> = var>
exprSim← (var (inj₁ refl)) ((poi {n< = n<₁} , snd) ∷ mrel) (poi {n< = n<}) var> rewrite leq n< n<₁ = var>
exprSim← (var (inj₁ refl)) ((undef , snd) ∷ mrel) undef var> = var>
exprSim← (var (inj₂ refl)) ((fst , unit) ∷ mrel) unit var> = var>
exprSim← (var (inj₂ refl)) ((fst , nat) ∷ mrel) nat var> = var>
exprSim← (var (inj₂ refl)) ((fst , poi {n< = n<₁}) ∷ mrel) (poi {n< = n<}) var> rewrite leq n< n<₁ = var>
exprSim← (var (inj₂ refl)) ((fst , undef) ∷ mrel) undef var> = var>
exprSim← {L = L} (& x) mrel (poi {n< = n<}) &> rewrite leq n< ≤′-refl = &>
exprSim← (* e) mrel vrel (*> {a = a} ev a∈M)
  rewrite ↝≡ vrel (getRel← mrel a a∈M) = S.*> (exprSim← e mrel (poi {n< = a∈M}) ev)

-- The ∼ relation is not a bisimulation

-- A simple example on function calls
-- CHERI does not allow passing or returning of local capabilities

P1 : Prog (record { a = Unit ; r = Unit } ∷ (record { a = Ref Unit ; r = Unit } ∷ []))
P1 = ((record { ret = Unit ; ns = Unit ∣ Unit ; body = call (there (here refl)) (& (inj₁ refl)) $ (return unit) }) , rfl) ∷
     ((record { ret = Unit ; ns = (Ref Unit) ∣ Unit ; body = return unit } , rfl) ∷ [])


absurd-cmdsim→ : ({X : Exports} {P : Prog X} {L₁ L₂ : StoreTy} {S₁ : State X L₁} {S₂ : State X L₂}
                 {C₁ : CapState X L₁} → S₁ ∼ C₁ →  P ⊨ S₁ ⟶ S₂ → Σ[ C₂ ∈ CapState X L₂ ] (S₂ ∼ C₂ × P ⊩ C₁ ⟶ C₂)) → ⊥
absurd-cmdsim→ P with P {X = (record { a = Unit ; r = Unit }) ∷ record { a = Ref Unit ; r = Unit } ∷ []}
                        {P = P1}
                        {L₁ = (Unit ∣ Unit) ∷ []} {L₂ = ((Ref Unit) ∣ Unit) ∷ ((Unit ∣ Unit) ∷ [])}
                        {S₁ = ((unit - unit) ∷ []) ↓ ((call (there (here refl)) (& (inj₁ refl)) $ (return unit)) ∷ []) ↓ (nothing ∷ [])}
                        {S₂ = ((loc (zero ⋆ ≤′-step ≤′-refl of false) - undef) ∷ ((unit - unit) ∷ [])) ↓ (return unit ∷ (return unit ∷ [])) ↓ (nothing ∷ (nothing ∷ []))}
                        ((unit , unit) ∷ [] , nn ∷ []) ((call> &>))
absurd-cmdsim→ P | .(((cap (0 of false) - undef) ∷ (unit - unit) ∷ []) ⅋ return unit ∷ (return unit ∷ []) ⅋ (nothing ∷ nothing ∷ [])) , (x , x₁) , call> &> ()

-- Opposite direction
-- Our scoped language (ideal C) does not allow "unsafe" assignments
-- CHERI, making no distinction for the lifetimes of local capabilities, allows it
-- The absurd pattern comes from the absurdity of the ≤-contract for the Store (2 ≤ 0)

P2 : Prog (record { a = Unit ; r = Unit } ∷ (record { a = Ref (Ref Unit) ; r = Unit } ∷ []))
P2 = ((record { ret = Unit ; ns = Unit ∣ Ref Unit ; body = call (there (here refl)) (& (inj₂ refl)) $ (return unit) }) , rfl) ∷
     ((record { ret = Unit ; ns = Ref (Ref Unit) ∣ Unit ; body = (var (inj₁ refl) := & (inj₂ refl)) $ return unit } , rfl) ∷ [])

L : StoreTy
L = (Ref (Ref Unit) ∣ Unit) ∷ ((Unit ∣ Ref Unit) ∷ [])

absurd-cmdsim← : ({X : Exports} {P : Prog X} {L₁ L₂ : StoreTy} {S₁ : State X L₁}
                 {C₁ : CapState X L₁} {C₂ : CapState X L₂} → S₁ ∼ C₁ → P ⊩ C₁ ⟶ C₂ → Σ[ S₂ ∈ State X L₂ ] (S₂ ∼ C₂ × P ⊨ S₁ ⟶ S₂)) → ⊥
absurd-cmdsim← P with P {X = record { a = Unit ; r = Unit } ∷ (record { a = Ref (Ref Unit) ; r = Unit } ∷ [])}
                        {P = P2} {L₁ = L} {L₂ = L}
                        {C₁ = ((cap (0 of true) - undef) ∷ ((unit - undef) ∷ [])) ⅋ (((var (inj₁ refl) := & (inj₂ refl)) $ return unit) ∷ (return unit ∷ [])) ⅋ (nothing ∷ (nothing ∷ []))}
                        {C₂ = ((cap (0 of true) - undef) ∷ ((unit - cap (1 of true)) ∷ [])) ⅋ return unit $ return unit ∷ (return unit) ∷ [] ⅋ (nothing ∷ (nothing ∷ []))}
                        (((poi {n< = ≤′-step ≤′-refl} , undef) ∷ ((unit , undef) ∷ [])) , nn ∷ (nn ∷ [])) ($> (:=> var> &> (≤′-step ≤′-refl)))
absurd-cmdsim← P | (.(_ ∷ ((_ - loc (1 ⋆ ≤′-step _ of true)) ∷ _)) ↓ .((return unit $ return unit) ∷ (return unit ∷ [])) ↓ ret) , ((x ∷ ((fst , poi {n< = ≤′-step ()}) ∷ x₃)) , x₁) , snd

