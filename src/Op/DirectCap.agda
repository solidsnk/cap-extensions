module Op.DirectCap where

open import Data.Nat
open import Data.List hiding (lookup)
open import Data.List.All
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Reverse
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Maybe hiding (All)
open import Data.Bool using (Bool ; true ; false)
open import Data.Product
open import Relation.Nullary

open import Op.SourceSyntax

record Addr : Set where
  constructor _of_
  field
    base : ℕ
    off : Bool

-- Values do not depend on the memory state
-- References are untyped
-- Needs explicit freshness to work
data Cval : Set where
  unit : Cval
  nat : ℕ → Cval
  cap : Addr → Cval
  undef : Cval

data !Cap : Cval → Set where
  unit! : !Cap unit
  nat : ∀ {n} → !Cap (nat n)

-- Memory and values
record Cell : Set where
  constructor _-_
  field
    a : Cval
    v : Cval

-- Memory is a list of allocations and their values
-- This represents that available memory is always tied to an allocation
-- In this case just function frames
-- Unlike in the abstract semantics, there is no guarantee against dangling
-- pointers, just like in a real processor
Memory : StoreTy → Set
Memory L = All (λ _ → Cell) L

Cret : StoreTy → Set
Cret L = All (λ _ → Maybe Addr) L

_|∈|_ : ∀ {L : StoreTy} → Addr → Memory L → Set
_|∈|_ {L} (base of s) m = base <′ length L

select : Bool → Cell → Cval
select false c = Cell.a c
select true c = Cell.v c

new : Bool → Cval → Cell → Cell
new false v c = v - (Cell.v c)
new true v c = (Cell.a c) - v

get : ∀ {L} → (a : Addr) → (M : Memory L) → a |∈| M → Cval
get a [] ()
get (.(foldr (λ _ → suc) 0 xs) of off) (_∷_ {xs = xs} px M) ≤′-refl = select off px
get (base of off) (_∷_ {xs = xs} px M) (≤′-step a∈) = get (base of off) M a∈

update : ∀ {L} → (a : Addr) → (M : Memory L) → a |∈| M → Cval → Memory L
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
  &> : ∀ {t} {v : t ⊢ Γ} → M ⊩ & v ⇒ cap (length L of vToBool v)
  *> : ∀ {t} {expr : Expr Γ (Ref t)} {a : Addr}
       → M ⊩ expr ⇒ (cap a) → (a∈M : a |∈| M) → M ⊩ (* expr) ⇒ get a M a∈M

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
        → ∀ {a : Addr} {v : Cval}
        → M ⊩ left ⇒ cap a → M ⊩ right ⇒ v → (a∈M : a |∈| M)
        → P ⊩ M ⅋ ((left := right) ∷ C) ⅋ R ⟶ update a M a∈M v ⅋ (return unit ∷ C) ⅋ R
  endN> : ∀ {L} {Γ} {M : Memory (Γ ∷ L)} {c : Cell} {C} {t} {e : Expr Γ t} {R}
          → P ⊩ (c ∷ M) ⅋ return e ∷ C ⅋ (nothing ∷ R) ⟶ M ⅋ C ⅋ R
  end←> : ∀ {L} {Γ} {M : Memory (Γ ∷ L)} {c : Cell} {C} {t} {e : Expr Γ t} {R} {v} {a}
          → M ⊩ e ⇒ v → !Cap v → (a∈M : a |∈| M)
          → P ⊩ (c ∷ M) ⅋ return e ∷ C ⅋ (just a ∷ R) ⟶ update a M a∈M v ⅋ C ⅋ R
  call> : ∀ {L} {Γ} {t} {M : Memory (Γ ∷ L)} {d} {d∈ : d ∈ X} {arg : Expr Γ (Decl.a d)} {v} {C} {c : Cmd X Γ t} {R}
          → M ⊩ arg ⇒ v → !Cap v → P ⊩ M ⅋ (call d∈ arg $ c) ∷ C ⅋ R
          ⟶ (((v - undef) ∷ M) ⅋ FunDef.body (getDef P d∈) ∷ (c ∷ C) ⅋ (nothing ∷ R))
  c←> : ∀ {L} {Γ} {t} {M : Memory (Γ ∷ L)} {d} {d∈ : d ∈ X} {arg : Expr Γ (Decl.a d)} {r : Expr Γ (Ref (Decl.r d))}
          {v} {C} {c : Cmd X Γ t} {R} {a}
        → M ⊩ arg ⇒ v → !Cap v → M ⊩ r ⇒ cap a → P ⊩ M ⅋ (c← d∈ arg r $ c) ∷ C ⅋ R
        ⟶ ((v - undef) ∷ M) ⅋ FunDef.body (getDef P d∈) ∷ (c ∷ C) ⅋ (just a ∷ R)
