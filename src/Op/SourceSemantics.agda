module Op.SourceSemantics where

open import Data.Nat
open import Data.List
open import Data.List.Any
open import Data.List.All
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product
open import Data.Unit using (⊤ ; tt)
open import Data.Sum
open import Data.Empty
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Maybe hiding (All)

open import Op.SourceSyntax

-- A Loc containts a proof that an address is in bounds
record Loc (L : StoreTy) : Set where
  constructor _⋆_of_
  field
    base : ℕ
    proof : base <′ length L
    off : Bool

-- Values
data Val (L : StoreTy) : Set where
  unit : Val L
  nat : ℕ → Val L
  loc : Loc L → Val L
  undef : Val L

record Pair (L : StoreTy) : Set where
  constructor _-_
  field
    a : Val L
    v : Val L

-- Values increase monotonically
data Store : StoreTy → Set where
  [] : Store []
  _∷_ : ∀ {L} {Γ} → Pair (Γ ∷ L) → Store L → Store (Γ ∷ L)

tailS : ∀ {L} {Γ} → Store (Γ ∷ L) → Store L
tailS (x ∷ S) = S

data Ret : StoreTy → Set where
  [] : Ret []
  _∷_ : ∀ {L} {Γ} → Maybe (Loc L) → Ret L → Ret (Γ ∷ L)

wkLoc : ∀ {L} → Loc L → (Γ : Ns) → Loc (Γ ∷ L)
wkLoc (base ⋆ proof of off) Γ = base ⋆ ≤′-step proof of off

wkVal : ∀ {L} → Val L → (Γ : Ns) → Val (Γ ∷ L)
wkVal unit Γ = unit
wkVal (nat x) Γ = nat x
wkVal (loc l) Γ = loc (wkLoc l Γ)
wkVal undef Γ = undef

get : ∀ {L} → Store L → Loc L → Val L
get [] (base ⋆ () of off)
get (_∷_ {L} x S) (.(foldr (λ _ → suc) 0 L) ⋆ ≤′-refl of false) = Pair.a x
get (_∷_ {L} x S) (.(foldr (λ _ → suc) 0 L) ⋆ ≤′-refl of true) = Pair.v x
get (_∷_ {L} {Γ} x S) (base ⋆ ≤′-step proof of off) = wkVal (get S (base ⋆ proof of off)) Γ

Up : ∀ {L} → Loc L → Val L → Set
Up l undef = ⊤
Up l unit = ⊤
Up l (nat x) = ⊤
Up (base₁ ⋆ proof₁ of off₁) (loc (base ⋆ proof of off)) = base ≤′ base₁

Up-wk : ∀ {L} {Γ} → (S : Store L) → (v : Val L) → (l : Loc L) →
        Up l v → Up (wkLoc l Γ) (wkVal v Γ)
Up-wk S undef l up = tt
Up-wk S unit l up = tt
Up-wk S (nat x) l up = tt
Up-wk S (loc x) l up = up

suc≤ : ∀ {n m} → suc n ≤′ suc m → n ≤′ m
suc≤ ≤′-refl = ≤′-refl
suc≤ {m = zero} (≤′-step ())
suc≤ {m = suc m} (≤′-step le) = ≤′-step (suc≤ le)

monoStore : ∀ {L} → (S : Store L) → (l : Loc L) → Up l (get S l)
basecase : ∀ {L} {Γ} → (S : Store L) → (a v : Val (Γ ∷ L)) → (off : Bool)
           → Up  (foldr (λ _ → suc) 0 L ⋆ ≤′-refl of off) (get ((a - v) ∷ S) (foldr (λ _ → suc) 0 L ⋆ ≤′-refl of off))
basecase S undef v false = tt
basecase S unit v false = tt
basecase S (nat x) v false = tt
basecase S (loc x) v false = suc≤ (Loc.proof x)
basecase S a undef true = tt
basecase S a unit true = tt
basecase S a (nat x) true = tt
basecase S a (loc x) true = suc≤ (Loc.proof x)
monoStore [] (base ⋆ () of off)
monoStore (_∷_ {L} (a - v) S) (.(foldr (λ _ → suc) 0 L) ⋆ ≤′-refl of off) = basecase S a v off
monoStore (_∷_ {L} x S) (base ⋆ ≤′-step proof of off)
  = Up-wk S (get S (base ⋆ proof of off)) (base ⋆ proof of off) (monoStore S (base ⋆ proof of off))

≤′-trans : ∀ {n₁ n₂ n₃} → n₁ ≤′ n₂ → n₂ ≤′ n₃ → n₁ ≤′ n₃
≤′-trans ≤′-refl le₂ = le₂
≤′-trans {n₃ = zero} (≤′-step le₁) ()
≤′-trans {n₃ = suc n₃} (≤′-step le₁) le₂ = ≤′-step (≤′-trans le₁ (suc≤ le₂))

sn≰n : ∀ {n} → suc n ≤′ n → ⊥
sn≰n {zero} ()
sn≰n {suc n} le = sn≰n (suc≤ le)

≤-contra : ∀ {n m} → n ≤′ m → suc m ≤′ n → ⊥
≤-contra le₁ le₂ = sn≰n (≤′-trans le₂ le₁)

update : ∀ {L} (S : Store L) → (l : Loc L) → (v : Val L) → Up l v → Store L
update [] (base ⋆ () of off) v up
update (_∷_ {L} x S) (.(foldr (λ _ → suc) 0 L) ⋆ ≤′-refl of false) v up = (v - Pair.v x) ∷ S
update (_∷_ {L} x S) (.(foldr (λ _ → suc) 0 L) ⋆ ≤′-refl of true) v up = (Pair.a x - v) ∷ S
update (_∷_ {L} x S) (base ⋆ ≤′-step proof of off) undef tt = x ∷ update S (base ⋆ proof of off) undef tt
update (_∷_ {L} x S) (base ⋆ ≤′-step proof of off) unit tt = x ∷ update S (base ⋆ proof of off) unit tt
update (_∷_ {L} x S) (base ⋆ ≤′-step proof of off) (nat x₁) tt = x ∷ update S (base ⋆ proof of off) (nat x₁) tt
update (_∷_ {L} x S) (base ⋆ ≤′-step proof of off) (loc (.(foldr (λ _ → suc) 0 L) ⋆ ≤′-refl of off₁)) up
  = ⊥-elim (≤-contra up proof)
update (_∷_ {L} x S) (base ⋆ ≤′-step proof of off) (loc (base₁ ⋆ ≤′-step proof₁ of off₁)) up
  = x ∷ update S (base ⋆ proof of off) (loc (base₁ ⋆ proof₁ of off₁)) up

-- Expression semantics are total
data _⊨_⇒_ {L} {Γ : Ns} (S : Store (Γ ∷ L)) :
             {t : Ty} → Expr Γ t → Val (Γ ∷ L) → Set where
  unit> : S ⊨ unit ⇒ unit
  nat> : ∀ {n} → S ⊨ nat n ⇒ nat n
  bOp> : ∀ {l r lz rz f} → S ⊨ l ⇒ nat lz → S ⊨ r ⇒ nat rz → S ⊨ bOp f l r ⇒ nat (f lz rz)
  var> : ∀ {t} {v : t ⊢ Γ} → S ⊨ var v ⇒ get S (length L ⋆ ≤′-refl of vToBool v)
  &> : ∀ {t} {v : t ⊢ Γ} → S ⊨ & v ⇒ loc ((foldr (λ _ → suc) zero L) ⋆ ≤′-refl of vToBool v)
  *> : ∀ {t} {n} {expr : Expr Γ (Ref t)} {n< : n <′ length (Γ ∷ L)} {b : Bool}
       → S ⊨ expr ⇒ loc (n ⋆ n< of b) → S ⊨ (* expr) ⇒ get S (n ⋆ n< of b)

-- States
record State (X : Exports) (L : StoreTy) : Set where
  constructor _↓_↓_
  field
    stack : Store L
    cmds : CmdStore X L
    ret : Ret L

infix 10 _⊨_⟶_

-- A helper
strValUp : ∀ {Γ} {L} → (l : Loc L) → (v : Val (Γ ∷ L)) →
           Up (wkLoc l Γ) v → Σ[ v' ∈ Val L ] Up l v'
strValUp l unit up = unit , tt
strValUp l (nat x) up = nat x , tt
strValUp {L = L} l (loc (.(foldr (λ _ → suc) 0 L) ⋆ ≤′-refl of off)) up = ⊥-elim (≤-contra up (Loc.proof l))
strValUp l (loc (base ⋆ ≤′-step proof of off)) up = loc (base ⋆ proof of off) , up
strValUp l undef up = undef , tt

-- Evaluation of commands
data _⊨_⟶_ {X : Exports} (P : Prog X) : {L₁ : StoreTy} {L₂ : StoreTy}
           → State X L₁ → State X L₂ → Set where
  ret> : ∀ {L} {Γ} {S : Store (Γ ∷ L)} {t} {c : Cmd X Γ t} {C} {t'} {E : Expr Γ t'} {R}
         → P ⊨ S ↓ ((return E $ c) ∷ C) ↓ R ⟶ S ↓ (c ∷ C) ↓ R
  $> : ∀ {L} {Γ} {S₁ S₂ : Store (Γ ∷ L)} {t} {c₁ c₂ : Cmd X Γ t} {t'} {c : Cmd X Γ t'} {C} {R}
       → P ⊨ S₁ ↓ (c₁ ∷ C) ↓ R ⟶ S₂ ↓ (c₂ ∷ C) ↓ R
       → P ⊨ S₁ ↓ ((c₁ $ c) ∷ C) ↓ R ⟶ S₂ ↓ ((c₂ $ c) ∷ C) ↓ R
  z> : ∀ {L} {Γ} {S : Store (Γ ∷ L)} {t} {c₁ c₂ : Cmd X Γ t} {C} {E : Expr Γ Nat} {R}
       → S ⊨ E ⇒ nat zero
       → P ⊨ S ↓ ((if E && c₁ || c₂) ∷ C) ↓ R ⟶ S ↓ (c₂ ∷ C) ↓ R
  !z> : ∀ {L} {Γ} {S : Store (Γ ∷ L)} {t} {c₁ c₂ : Cmd X Γ t} {C} {E : Expr Γ Nat} {k} {R}
        → S ⊨ E ⇒ nat (suc k)
        → P ⊨ S ↓ ((if E && c₁ || c₂) ∷ C) ↓ R ⟶ S ↓ (c₁ ∷ C) ↓ R
  :=> : ∀ {L} {Γ} {t} {S : Store (Γ ∷ L)} {left : Expr Γ (Ref t)} {right : Expr Γ t} {C} {R}
          {n : ℕ} {n< : n <′ length (Γ ∷ L)} {off} {v}
        → S ⊨ left ⇒ loc (n ⋆ n< of off) → S ⊨ right ⇒ v → (up : Up (n ⋆ n< of off) v)
        → P ⊨ S ↓ ((left := right) ∷ C) ↓ R ⟶ update S (n ⋆ n< of off) v up ↓ (return unit ∷ C) ↓ R
  -- end←> : ∀ {L} {Γ} {S : Store L} {p : Pair (Γ ∷ L)} {C} {t} {e : Expr Γ t} {v}
  --           {R : Ret L} {l : Loc L} → (p ∷ S) ⊨ e ⇒ v → (up : Up (wkLoc l Γ) v)
  --         → P ⊨ (p ∷ S) ↓ (return e ∷ C) ↓ ((just l) ∷ R) ⟶ tailS (update (p ∷ S) (wkLoc l Γ) v up) ↓ C ↓ R
  end←> : ∀ {L} {Γ} {S : Store L} {p : Pair (Γ ∷ L)} {C} {t} {e : Expr Γ t} {v}
          {R : Ret L} {l : Loc L} → (p ∷ S) ⊨ e ⇒ v → (up : Up (wkLoc l Γ) v)
          → P ⊨ (p ∷ S) ↓ (return e ∷ C) ↓ ((just l) ∷ R) ⟶ update S l (proj₁ (strValUp l v up)) ((proj₂ (strValUp l v up))) ↓ C ↓ R
  endN> : ∀ {L} {Γ} {S : Store L} {p : Pair (Γ ∷ L)} {C} {t} {e : Expr Γ t} {R}
          → P ⊨ (p ∷ S) ↓ (return e ∷ C) ↓ (nothing ∷ R) ⟶ S ↓ C ↓ R
  call> : ∀ {L} {Γ} {t} {S : Store (Γ ∷ L)} {d} {d∈ : d ∈ X} {arg : Expr Γ (Decl.a d)} {v} {C} {c : Cmd X Γ t} {R}
          → S ⊨ arg ⇒ v → P ⊨ S ↓ ((call d∈ arg $ c) ∷ C) ↓ R
          ⟶ ((wkVal v (FunDef.ns (getDef P d∈)) - undef) ∷ S) ↓ (FunDef.body (getDef P d∈) ∷ (c ∷ C)) ↓ (nothing ∷ R)
  c←> : ∀ {L} {Γ} {t} {S : Store (Γ ∷ L)} {d} {d∈ : d ∈ X} {v} {C} {c : Cmd X Γ t} {R} {l}
          {arg : Expr Γ (Decl.a d)} {r : Expr Γ (Ref (Decl.r d))}
        → S ⊨ arg ⇒ v → S ⊨ r ⇒ loc l → P ⊨ S ↓ ((c← d∈ arg r $ c) ∷ C) ↓ R
           ⟶ ((wkVal v (FunDef.ns (getDef P d∈)) - undef) ∷ S)
           ↓ (FunDef.body (getDef P d∈) ∷ (c ∷ C)) ↓ (just l ∷ R)

-- Reflexive and transitive closure of the evaluation relation
data _⊨_⟶*_ {X : Exports} (P : Prog X) : {L₁ : StoreTy} {L₂ : StoreTy}
            → State X L₁ → State X L₂ → Set where
  done : ∀ {L} {S : State X L} → P ⊨ S ⟶* S
  step : ∀ {L₁ L₂ L₃} {S₁ : State X L₁} {S₂ : State X L₂} {S₃ : State X L₃}
         → P ⊨ S₁ ⟶ S₂ → P ⊨ S₂ ⟶* S₃ → P ⊨ S₁ ⟶* S₃

-- Termination (for filled contexts)
↓-ctx : ∀ {d} {z} {X} → (P : Prog (d ∷ z ∷ X)) → Set
↓-ctx P = P ⊨ ((undef - undef) ∷ []) ↓
               (FunDef.body (getDef P (there (here refl))) ∷ []) ↓
               (nothing ∷ []) ⟶* ([] ↓ [] ↓ [])

-- Contextual preorder
ctx→ : ∀ {d} {z} {X} → (f₁ f₂ : FunDef (d ∷ z ∷ X)) → f₁ |i| d → f₂ |i| d → Set
ctx→ f₁ f₂ i₁ i₂ = ∀ (c) → ↓-ctx (c ∣ f₁ ] i₁) → ↓-ctx (c ∣ f₂ ] i₂)

-- Contextual equivalence
≡-ctx : ∀ {d} {z} {X} → (f₁ f₂ : FunDef (d ∷ z ∷ X)) → f₁ |i| d → f₂ |i| d → Set
≡-ctx f₁ f₂ i₁ i₂ = ctx→ f₁ f₂ i₁ i₂ × ctx→ f₂ f₁ i₂ i₁
