module Op.DirectCapEx where

open import Data.Nat
open import Data.List hiding (lookup)
open import Data.List.Any
open import Data.List.All
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Reverse
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Maybe hiding (All)
open import Data.Bool using (Bool ; true ; false)
open import Data.Product
open import Relation.Nullary
open import Data.Unit using (⊤ ; tt)

open import Op.SourceSyntax

record Addr : Set where
  constructor _of_
  field
    base : ℕ
    off : Bool

data Cval : Set where
  unit : Cval
  nat : ℕ → Cval
  cap : Addr → ℕ → Cval
  undef : Cval

Safe : ℕ → Cval → Set
Safe f unit = ⊤
Safe f (nat x) = ⊤
Safe f (cap a' f') = f' ≤′ f
Safe f undef = ⊤

-- Memory and values
record Cell : Set where
  constructor _-_
  field
    a : Cval
    v : Cval

Memory : StoreTy → Set
Memory L = All (λ _ → Cell) L

Cret : StoreTy → Set
Cret L = All (λ _ → Maybe (Addr × ℕ)) L

_|∈|_ : Addr → StoreTy → Set
_|∈|_ (base of s) L = base <′ length L

Valid : StoreTy → Cval → Set
Valid L unit = ⊤
Valid L (nat x) = ⊤
Valid L (cap a f) = a |∈| L
Valid L undef = ⊤

select : Bool → Cell → Cval
select false c = Cell.a c
select true c = Cell.v c

new : Bool → Cval → Cell → Cell
new false v c = v - (Cell.v c)
new true v c = (Cell.a c) - v

get : ∀ {L} → (a : Addr) → (M : Memory L) → a |∈| L → Cval
get a [] ()
get (.(foldr (λ _ → suc) 0 xs) of off) (_∷_ {xs = xs} px M) ≤′-refl = select off px
get (base of off) (_∷_ {xs = xs} px M) (≤′-step a∈) = get (base of off) M a∈

update : ∀ {L} → (a : Addr) → (M : Memory L) → a |∈| L → Cval → Memory L
update a [] () v
update (.(foldr (λ _ → suc) 0 xs) of off) (_∷_ {xs = xs} px M) ≤′-refl v = new off v px ∷ M
update (base of off) (_∷_ {xs = xs} px M) (≤′-step a∈) v = px ∷ (update (base of off) M a∈ v)

-- Evaluation of expressions
data _⊩_⇒_ {L : StoreTy} {Γ : Ns} (M : Memory (Γ ∷ L)) :
     {t : Ty} → Expr Γ t → Cval → Set where
  unit> : M ⊩ unit ⇒ unit
  nat> : ∀ {n} → M ⊩ nat n ⇒ nat n
  bOp> : ∀ {l r lz rz f} → M ⊩ l ⇒ nat lz → M ⊩ r ⇒ nat rz → M ⊩ bOp f l r ⇒ nat (f lz rz)
  var> : ∀ {t} {v : t ⊢ Γ} → M ⊩ var v ⇒ select (vToBool v) (head M)
  &> : ∀ {t} {v : t ⊢ Γ} → M ⊩ & v ⇒ cap (length L of vToBool v) (length L)
  *> : ∀ {t} {n} {expr : Expr Γ (Ref t)} {a : Addr}
       → M ⊩ expr ⇒ (cap a n) → (a∈M : a |∈| (Γ ∷ L)) → M ⊩ (* expr) ⇒ get a M a∈M -- debatable

record CapState (X : Exports) (L : StoreTy) : Set where
  constructor _⅋_⅋_
  field
    mem : Memory L
    cmd : CmdStore X L
    ret : Cret L

infix 10 _⊩_⟶_

-- Evaluation of commands
data _⊩_⟶_ {X : Exports} (P : Prog X) : {L₁ : StoreTy} {L₂ : StoreTy}
           → CapState X L₁ → CapState X L₂ → Set where
  ret> : ∀ {L} {Γ} {M : Memory (Γ ∷ L)} {t} {c : Cmd X Γ t} {C} {t'} {E : Expr Γ t'} {R}
         → P ⊩ M ⅋ ((return E $ c) ∷ C) ⅋ R ⟶ M ⅋ (c ∷ C) ⅋ R
  $> : ∀ {L} {Γ} {M₁ M₂ : Memory (Γ ∷ L)} {t} {c₁ c₂ : Cmd X Γ t} {t'} {c : Cmd X Γ t'} {C} {R}
       → P ⊩ M₁ ⅋ (c₁ ∷ C) ⅋ R ⟶ M₂ ⅋ (c₂ ∷ C) ⅋ R
       → P ⊩ M₁ ⅋ ((c₁ $ c) ∷ C) ⅋ R ⟶ M₂ ⅋ ((c₂ $ c) ∷ C) ⅋ R
  z> : ∀ {L} {Γ} {M : Memory (Γ ∷ L)} {t} {c₁ c₂ : Cmd X Γ t} {C} {E : Expr Γ Nat} {R}
       → M ⊩ E ⇒ nat zero
       → P ⊩ M ⅋ ((if E && c₁ || c₂) ∷ C) ⅋ R ⟶ M ⅋ (c₂ ∷ C) ⅋ R
  !z> : ∀ {L} {Γ} {M : Memory (Γ ∷ L)} {t} {c₁ c₂ : Cmd X Γ t} {C} {E : Expr Γ Nat} {n} {R}
        → M ⊩ E ⇒ nat (suc n)
        → P ⊩ M ⅋ ((if E && c₁ || c₂) ∷ C) ⅋ R ⟶ M ⅋ (c₁ ∷ C) ⅋ R
  :=> : ∀ {L} {Γ} {M : Memory (Γ ∷ L)} {t} {left : Expr Γ (Ref t)} {right : Expr Γ t} {C} {R}
        → ∀ {a : Addr} {v : Cval} {n}
        → M ⊩ left ⇒ cap a n → M ⊩ right ⇒ v → (a∈M : a |∈| (Γ ∷ L)) → Safe n v
        → P ⊩ M ⅋ ((left := right) ∷ C) ⅋ R ⟶ update a M a∈M v ⅋ (return unit ∷ C) ⅋ R
  endN> : ∀ {L} {Γ} {M : Memory L} {c : Cell} {C} {t} {e : Expr Γ t} {R}
          → P ⊩ (c ∷ M) ⅋ return e ∷ C ⅋ (nothing ∷ R) ⟶ M ⅋ C ⅋ R
  end←> : ∀ {L} {Γ} {M : Memory L} {c : Cell} {C} {t} {e : Expr Γ t} {R} {v} {a} {n}
          → (c ∷ M) ⊩ e ⇒ v → (a∈M : a |∈| L) → Safe n v
          → P ⊩ (c ∷ M) ⅋ return e ∷ C ⅋ (just (a , n) ∷ R) ⟶ update a M a∈M v ⅋ C ⅋ R
  call> : ∀ {L} {Γ} {t} {M : Memory (Γ ∷ L)} {d} {d∈ : d ∈ X} {arg : Expr Γ (Decl.a d)} {v} {C} {c : Cmd X Γ t} {R}
          → M ⊩ arg ⇒ v → P ⊩ M ⅋ (call d∈ arg $ c) ∷ C ⅋ R
          ⟶ (((v - undef) ∷ M) ⅋ FunDef.body (getDef P d∈) ∷ (c ∷ C) ⅋ (nothing ∷ R))
  c←> : ∀ {L} {Γ} {t} {M : Memory (Γ ∷ L)} {d} {d∈ : d ∈ X} {arg : Expr Γ (Decl.a d)} {r : Expr Γ (Ref (Decl.r d))}
          {v} {C} {c : Cmd X Γ t} {R} {a} {n}
        → M ⊩ arg ⇒ v → M ⊩ r ⇒ cap a n → P ⊩ M ⅋ (c← d∈ arg r $ c) ∷ C ⅋ R
        ⟶ ((v - undef) ∷ M) ⅋ FunDef.body (getDef P d∈) ∷ (c ∷ C) ⅋ (just (a , n) ∷ R)

-- Reflexive and transitive closure of the evaluation relation
data _⊩_⟶*_ {X : Exports} (P : Prog X) : {L₁ : StoreTy} {L₂ : StoreTy}
             → CapState X L₁ → CapState X L₂ → Set where
  done : ∀ {L} {C : CapState X L} → P ⊩ C ⟶* C
  step : ∀ {L₁ L₂ L₃} {C₁ : CapState X L₁} {C₂ : CapState X L₂} {C₃ : CapState X L₃}
         → P ⊩ C₁ ⟶ C₂ → P ⊩ C₂ ⟶* C₃ → P ⊩ C₁ ⟶* C₃

-- Termination (for filled contexts)
↓-ctx : ∀ {d} {z} {X} → (P : Prog (d ∷ z ∷ X)) → Set
↓-ctx P = P ⊩ ((undef - undef) ∷ []) ⅋
               (FunDef.body (getDef P (there (here refl))) ∷ []) ⅋
               (nothing ∷ []) ⟶* ([] ⅋ [] ⅋ [])

-- Contextual preorder
ctx→ : ∀ {d} {z} {X} → (f₁ f₂ : FunDef (d ∷ z ∷ X)) → f₁ |i| d → f₂ |i| d → Set
ctx→ f₁ f₂ i₁ i₂ = ∀ (c) → ↓-ctx (c ∣ f₁ ] i₁) → ↓-ctx (c ∣ f₂ ] i₂)

-- Contextual equivalence
≡-ctx : ∀ {d} {z} {X} → (f₁ f₂ : FunDef (d ∷ z ∷ X)) → f₁ |i| d → f₂ |i| d → Set
≡-ctx f₁ f₂ i₁ i₂ = ctx→ f₁ f₂ i₁ i₂ × ctx→ f₂ f₁ i₂ i₁
