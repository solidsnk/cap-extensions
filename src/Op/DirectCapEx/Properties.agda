module Op.DirectCapEx.Properties where

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

data +M {A B : Set} (P : A → B → Set) : Maybe A → Maybe B → Set where
  nn : +M P nothing nothing
  jj : ∀ {a} {b} → P a b → +M P (just a) (just b)

data _⇌_ {L : StoreTy} : Loc L → (Addr × ℕ) → Set where
  rfl : ∀ {n} {n< : n <′ length L} {b} → (n ⋆ n< of b) ⇌ ((n of b) , n)

data _|⇌|_ : {L : StoreTy} → Ret L → Cret L → Set where
  [] : [] |⇌| []
  _∷_ : ∀ {L : StoreTy} {Γ : Ns} {R : Ret L} {C : Cret L}
        {l : Maybe (Loc L)} {a : Maybe (Addr × ℕ)} →
        (+M _⇌_ ) l a → R |⇌| C → (_∷_ {Γ = Γ} l R) |⇌| (a ∷ C)

data _↝_ {L : StoreTy} : Val L → Cval → Set where
  unit : unit ↝ unit
  nat : ∀ {n} → nat n ↝ nat n
  poi : ∀ {n} {n< : n <′ length L} {b} → loc (n ⋆ n< of b) ↝ cap (n of b) n
  undef : undef ↝ undef

get↝ : ∀ {L} (v : Val L) → Σ[ c ∈ Cval ] (v ↝ c)
get↝ unit = unit , unit
get↝ (nat x) = nat x , nat
get↝ (loc (base ⋆ proof of off)) = cap (base of off) base , poi
get↝ undef = undef , undef

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
          → S |↝| M → (a : Addr) → (a∈M : a |∈| L)
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

↝Valid : ∀ {L} {v : Val L} {c} → v ↝ c → Valid L c
↝Valid unit = tt
↝Valid nat = tt
↝Valid (poi {n< = n<}) = n<
↝Valid undef = tt

Sane : Cval → Set
Sane unit = ⊤
Sane (nat x) = ⊤
Sane (cap (base of off) f) = base ≡ f
Sane undef = ⊤

↝f≡ : ∀ {L} {v : Val L} {c} → v ↝ c → Sane c
↝f≡ unit = tt
↝f≡ nat = tt
↝f≡ poi = refl
↝f≡ undef = tt

evSane : ∀ {L} {Γ} {t} {M : Memory (Γ ∷ L)} {S} {e : Expr Γ t} {c}
      → S |↝| M → M ⊩ e ⇒ c → Sane c
evSane mrel unit> = tt
evSane mrel nat> = tt
evSane mrel (bOp> ev ev₁) = tt
evSane ((fst , snd) ∷ mrel) (var> {v = inj₁ refl}) = ↝f≡ fst
evSane ((fst , snd) ∷ mrel) (var> {v = inj₂ refl}) = ↝f≡ snd
evSane mrel &> = refl
evSane mrel (*> {a = a} ev a∈M) = ↝f≡ (getRel← mrel a a∈M)

evValid : ∀ {L} {Γ} {t} {M : Memory (Γ ∷ L)} {S} {e : Expr Γ t} {v}
         → S |↝| M → M ⊩ e ⇒ v → Valid (Γ ∷ L) v
evValid mrel unit> = tt
evValid mrel nat> = tt
evValid mrel (bOp> ev ev₁) = tt
evValid ((fst , snd) ∷ mrel) (var> {v = inj₁ refl}) = ↝Valid fst
evValid ((fst , snd) ∷ mrel) (var> {v = inj₂ refl}) = ↝Valid snd
evValid mrel &> = ≤′-refl
evValid {M = M} mrel (*> {a = a} ev a∈M) = ↝Valid (getRel← mrel a a∈M)

teg↝ : ∀ {L : StoreTy} → (c : Cval) → Valid L c → Sane c → Σ[ v ∈ Val L ] (v ↝ c)
teg↝ unit sane eq = unit , unit
teg↝ (nat x) sane eq = nat x , nat
teg↝ (cap (base of off) f) sane refl = loc (base ⋆ sane of off) , poi
teg↝ undef sane eq = undef , undef

exprSim← : ∀ {t} {L : StoreTy} {Γ : Ns} {S : Store (Γ ∷ L)}
           (e : Expr Γ t) {v : Val (Γ ∷ L)} {cv : Cval} {M : Memory (Γ ∷ L)} →
           S |↝| M → v ↝ cv → M ⊩ e ⇒ cv → S ⊨ e ⇒ v
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
exprSim← (& x) mrel (poi {n< = n<}) &> rewrite leq n< ≤′-refl = &>
exprSim← (* e) mrel vrel (*> {a = a} ev a∈M) with evSane mrel ev
... | refl rewrite ↝≡ vrel (getRel← mrel a a∈M) = S.*> (exprSim← e mrel (poi {n< = a∈M}) ev)

≡|↝| : ∀ {L} {S : Store L} {M M'} → S |↝| M → S |↝| M' → M ≡ M'
≡|↝| [] [] = refl
≡|↝| (_∷_ {c = a - v} (rf , rs) R) (_∷_ {c = a₁ - v₁} (rf' , rs') R')
  rewrite ≡↝ rf rf' | ≡↝ rs rs' | ≡|↝| R R' = refl

≡⇌ : ∀ {L} {l : Maybe (Loc L)} {a a' : Maybe (Addr × ℕ)} → +M _⇌_ l a → +M _⇌_ l a' → a ≡ a'
≡⇌ nn nn = refl
≡⇌ (jj rfl) (jj rfl) = refl

≡|⇌| : ∀ {L} {R : Ret L} {C C' : Cret L} → R |⇌| C → R |⇌| C' → C ≡ C'
≡|⇌| [] [] = refl
≡|⇌| (x ∷ r) (x' ∷ r') rewrite ≡⇌ x x' | ≡|⇌| r r' = refl

update|↝| : ∀ {L} {S : Store L} {M : Memory L} {v : Val L} {c : Cval} {n} {n<} {off} {up}
            → S |↝| M → v ↝ c → S.update S (n ⋆ n< of off) v up |↝| C.update (n of off) M n< c
update|↝| {n< = ()} [] v
update|↝| {n< = ≤′-refl} {false} (x ∷ mrel) v = (v , (proj₂ x)) ∷ mrel
update|↝| {n< = ≤′-refl} {true} (x ∷ mrel) v = ((proj₁ x) , v) ∷ mrel
update|↝| {n< = ≤′-step n<} (x ∷ mrel) unit = x ∷ update|↝| mrel unit
update|↝| {n< = ≤′-step n<} (x ∷ mrel) nat = x ∷ update|↝| mrel nat
update|↝| {n< = ≤′-step n<} {up = up} (x ∷ mrel) (poi {n< = ≤′-refl}) = ⊥-elim (≤-contra up n<)
update|↝| {n< = ≤′-step n<} (x ∷ mrel) (poi {n< = ≤′-step n<₁}) = x ∷ update|↝| mrel poi
update|↝| {n< = ≤′-step n<} (x ∷ mrel) undef = x ∷ update|↝| mrel undef

safe↝Up : ∀ {L} {n} {cv} {v : Val L} {n<} {b} →
          Safe n cv → v ↝ cv → Up (n ⋆ n< of b) v
safe↝Up safe unit = tt
safe↝Up safe nat = tt
safe↝Up safe poi = safe
safe↝Up safe undef = tt

st↝ : ∀ {L} {Γ} {v : Val (Γ ∷ L)} {cv} {l : Loc L} {up : Up (wkLoc l Γ) v} →
      v ↝ cv → (proj₁ (strValUp l v up)) ↝ cv
st↝ unit = unit
st↝ nat = nat
st↝ {l = base ⋆ proof of off} {up} (poi {n< = ≤′-refl}) = ⊥-elim (≤-contra up proof)
st↝ {l = base ⋆ proof of off} (poi {n< = ≤′-step n<}) = poi
st↝ undef = undef
