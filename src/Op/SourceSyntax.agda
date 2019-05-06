module Op.SourceSyntax where

open import Data.Nat
open import Data.List hiding (lookup)
open import Data.List.Any
open import Data.List.All
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality
open import Data.Sum

open import Data.Fin
open import Data.Bool
open import Data.Product

-- Simple datatypes
data Ty : Set where
  Unit : Ty
  Nat : Ty
  Ref : Ty → Ty

-- A local namespace
record NameSpace (A : Set) : Set where
  constructor _∣_
  field
    arg : A
    var : A
--    var : List A

Ns = NameSpace Ty

-- For singletons
_⊢_ : ∀ {A : Set} → A → NameSpace A → Set
x ⊢ (arg ∣ var) = (x ≡ arg) ⊎ (x ≡ var) -- (x |∈| var)

-- Other utilities
vToBool : ∀ {t : Ty} {Γ} (v : t ⊢ Γ) → Bool
vToBool (inj₁ x) = false
vToBool (inj₂ y) = true

data Expr (Γ : Ns) : Ty → Set where
  nat : ℕ → Expr Γ Nat
  unit : Expr Γ Unit
  bOp : (ℕ → ℕ → ℕ) → Expr Γ Nat → Expr Γ Nat → Expr Γ Nat
  var : ∀ {t} → t ⊢ Γ → Expr Γ t
  & : ∀ {t} → t ⊢ Γ → Expr Γ (Ref t)
  * : ∀ {t} → Expr Γ (Ref t) → Expr Γ t

-- A record for declarations/exports
record Decl : Set where
  field
    a : Ty
    r : Ty

Exports = List Decl

-- Needed for both source and cap semantics
StoreTy = List Ns

data Cmd (X : Exports) (Γ : Ns) : Ty → Set where
  return : ∀ {t} → Expr Γ t → Cmd X Γ t
  _:=_  : ∀ {t} → Expr Γ (Ref t) → Expr Γ t → Cmd X Γ Unit
  _$_ : ∀ {t₁ t₂} → Cmd X Γ t₁ → Cmd X Γ t₂ → Cmd X Γ t₂
  if_&&_||_ : ∀ {t} → Expr Γ Nat → Cmd X Γ t → Cmd X Γ t → Cmd X Γ t
  call : ∀ {decl} → decl ∈ X → Expr Γ (Decl.a decl) → Cmd X Γ Unit
  c← : ∀ {decl} → decl ∈ X → Expr Γ (Decl.a decl) →
       Expr Γ (Ref (Decl.r decl)) → Cmd X Γ Unit

record FunDef (X : Exports) : Set where
  field
    ret : Ty
    ns : Ns
    body : Cmd X ns ret

-- Function implements declaration
data _|i|_ {X : Exports} : FunDef X → Decl → Set where
  rfl : ∀ {t} {ns} {b : Cmd X ns t} →
    (record { ret = t ; ns = ns ; body = b }) |i|
    (record { r = t ; a = NameSpace.arg ns })

DefList : Exports → Exports → Set
DefList X Y = All (λ x → Σ[ fd ∈ FunDef X ] (fd |i| x)) Y

-- A program is a list of commands that implement their typing context
Prog : Exports → Set
Prog X = DefList X X

getDef : ∀ {X} {Y} {d} → DefList X Y → d ∈ Y → FunDef X
getDef defs sym = proj₁ (lookup defs sym)

data CmdStore (X : Exports) : StoreTy → Set where
  [] : CmdStore X []
  _∷_ : ∀ {L} {Γ} {t} → Cmd X Γ t → CmdStore X L → CmdStore X (Γ ∷ L)

-- Program contexts
-- Contexts are programs with a function hole
-- The second function is main
Ctx : Decl → Decl → Exports → Set
Ctx d m X = DefList (d ∷ m ∷ X) (m ∷ X)

_∣_]_ : ∀ {d} {m} {X} → Ctx d m X → (def : FunDef (d ∷ m ∷ X)) → def |i| d → Prog (d ∷ m ∷ X)
ctx ∣ def ] impl = (def , impl) ∷ ctx
