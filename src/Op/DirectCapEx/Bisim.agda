module Op.DirectCapEx.Bisim where

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

cmdSim→ : ∀ {X : Exports} {P : Prog X} {L₁ L₂ : StoreTy} {S₁ : State X L₁} {S₂ : State X L₂}
          {C₁ : CapState X L₁} → S₁ ∼ C₁ →  P ⊨ S₁ ⟶ S₂ → ∃ λ C₂ → (S₂ ∼ C₂ × P ⊩ C₁ ⟶ C₂)
cmdSim→ ([] , []) ()

cmdSim→ (_∷_ {M = M} {c = c₁} srel Srel , _∷_ {C = C₁} {a = a} rrel Rrel) (ret> {c = c} {C})
        = ((c₁ ∷ M) ⅋ c ∷ C ⅋ (a ∷ C₁)) , ((srel ∷ Srel , rrel ∷ Rrel) , ret>)

cmdSim→ (srel ∷ Srel , rrel ∷ Rrel) ($> ev) with cmdSim→ (srel ∷ Srel , rrel ∷ Rrel) ev
cmdSim→ (srel ∷ Srel , rrel ∷ Rrel) ($> ev) | .((_ ∷ _) ⅋ _ ∷ _ ⅋ (_ ∷ _)) ,
        (sr ∷ Sr , rr ∷ Rr) , snd with ≡⇌ rrel rr | ≡|⇌| Rr Rrel
cmdSim→ (_∷_ {M = M₁} srel Srel , (rrel ∷ Rrel)) ($> {c₂ = c₂} {c = c₄} {C₁} ev) |
        .((c ∷ M) ⅋ c₂ ∷ C₁ ⅋ (a ∷ C)) , (_∷_ {M = M} {c = c} sr Sr , _∷_ {C = C} {a = a} rr Rr) , snd | refl |
        refl = ((c ∷ M) ⅋ (c₂ $ c₄) ∷ C₁ ⅋ (a ∷ C)) , ((sr ∷ Sr , rr ∷ Rr) , ($> snd))

cmdSim→ (_∷_ {M = M} {c = c₁} srel Srel , _∷_ {C = C₁} {a = a} rrel Rrel)
        (z> {c₁ = c₂} {c₃} {C} {E} x)
         = (c₁ ∷ M) ⅋ c₃ ∷ C ⅋ (a ∷ C₁) , (srel ∷ Srel , rrel ∷ Rrel)
           , (z> (exprSim→ E (srel ∷ Srel) nat x))

cmdSim→ (_∷_ {M = M} {c = c₁} srel Srel , _∷_ {C = C₁} {a = a} rrel Rrel)
        (!z> {c₁ = c₂} {c₃} {C} {E} x)
        = (c₁ ∷ M) ⅋ c₂ ∷ C ⅋ (a ∷ C₁) , (srel ∷ Srel , rrel ∷ Rrel)
          , (!z> (exprSim→ E (srel ∷ Srel) nat x))

cmdSim→ (_∷_ {M = M} {c = c} srel Srel , _∷_ {C = C₁} {a = a} rrel Rrel)
        (:=> {left = left} {right} {C} {n = n} {n<} {off} {unit} evl evr up)
        = (C.update (n of off) (c ∷ M) n< unit ⅋ return unit ∷ C ⅋ (a ∷ C₁))
          , ((update|↝| (srel ∷ Srel) unit , rrel ∷ Rrel)
          , :=> (exprSim→ left (srel ∷ Srel) poi evl) (exprSim→ right (srel ∷ Srel) unit evr)  n< tt)

cmdSim→ (_∷_ {M = M} {c = c} srel Srel , _∷_ {C = C₁} {a = a} rrel Rrel)
        (:=> {left = left} {right} {C} {n = n} {n<} {off} {nat x} evl evr up)
        = (C.update (n of off) (c ∷ M) n< (nat x) ⅋ return unit ∷ C ⅋ (a ∷ C₁))
          , ((update|↝| (srel ∷ Srel) nat , rrel ∷ Rrel)
          , :=> (exprSim→ left (srel ∷ Srel) poi evl) (exprSim→ right (srel ∷ Srel) nat evr) n< tt)

cmdSim→ (_∷_ {M = M} {c = c} srel Srel , _∷_ {C = C₁} {a = a} rrel Rrel)
        (:=> {left = left} {right} {C} {n = n} {n<} {off} {loc (base ⋆ proof of off₁)} evl evr up)
        = (C.update (n of off) (c ∷ M) n< (cap (base of off₁) base)
          ⅋ return unit ∷ C ⅋ (a ∷ C₁))
          , ((update|↝| (srel ∷ Srel) poi , rrel ∷ Rrel)
          , :=> (exprSim→ left (srel ∷ Srel) poi evl) (exprSim→ right (srel ∷ Srel) poi evr) n< up)

cmdSim→ (_∷_ {M = M} {c = c} srel Srel , _∷_ {C = C₁} {a = a} rrel Rrel)
        (:=> {left = left} {right} {C} {n = n} {n<} {off} {undef} evl evr up)
        = (C.update (n of off) (c ∷ M) n< undef ⅋ return unit ∷ C ⅋ (a ∷ C₁))
          , ((update|↝| (srel ∷ Srel) undef , rrel ∷ Rrel)
          , :=> (exprSim→ left (srel ∷ Srel) poi evl) (exprSim→ right (srel ∷ Srel) undef evr) n< tt)

cmdSim→ (_∷_ {M = M} {c = c} srel Srel , _∷_ {C = C} (jj (rfl {n} {n<} {b})) Rrel)
        (end←> {C = cmds} {e = e} {unit} ret up)
        = (C.update (n of b) M n< unit ⅋ cmds ⅋ C) , ((update|↝| Srel unit , Rrel)
          , (end←> (exprSim→ e (srel ∷ Srel) unit ret) n< tt))

cmdSim→ (_∷_ {M = M} {c = c} srel Srel , _∷_ {C = C} (jj (rfl {n} {n<} {b})) Rrel)
        (end←> {C = cmds} {e = e} {nat x} ret up)
        = (C.update (n of b) M n< (nat x) ⅋ cmds ⅋ C) , ((update|↝| Srel nat , Rrel)
          , (end←> (exprSim→ e (srel ∷ Srel) nat ret) n< tt))

cmdSim→ (_∷_ {L} {M = M} {c = c} srel Srel , _∷_ {C = C} (jj (rfl {n} {n<} {b})) Rrel)
        (end←> {C = cmds} {e = e} {loc (.(foldr (λ _ → suc) 0 L) ⋆ ≤′-refl of off)} ret up)
        = ⊥-elim (≤-contra up n<)
cmdSim→ (_∷_ {L} {M = M} {c = c} srel Srel , _∷_ {C = C} (jj (rfl {n} {n<} {b})) Rrel)
        (end←> {C = cmds} {e = e} {loc (base ⋆ ≤′-step proof of off)} ret up)
        = (C.update (n of b) M n< (cap (base of off) base) ⅋ cmds ⅋ C) , ((update|↝| Srel poi , Rrel)
          , (end←> (exprSim→ e (srel ∷ Srel) poi ret) n< up))

cmdSim→ (_∷_ {M = M} {c = c} srel Srel , _∷_ {C = C} (jj (rfl {n} {n<} {b})) Rrel)
        (end←> {C = cmds} {e = e} {undef} ret up)
        = (C.update (n of b) M n< undef ⅋ cmds ⅋ C) , ((update|↝| Srel undef , Rrel)
          , (end←> (exprSim→ e (srel ∷ Srel) undef ret) n< tt))

cmdSim→ (_∷_ {M = M} srel Srel , _∷_ {C = C} nn Rrel) (endN> {C = cmds})
        = (M ⅋ cmds ⅋ C) , ((Srel , Rrel) , endN>)

cmdSim→ {P = P} (_∷_ {M = M} {c = c₁} srel Srel , _∷_ {C = C₁} {a = a} rrel Rrel)
        (call> {d∈ = d∈} {arg} {v} {C} {c} eva)
        = (((proj₁ (get↝ v) - undef) ∷ (c₁ ∷ M))
          ⅋ FunDef.body (getDef P d∈) ∷ (c ∷ C) ⅋ (nothing ∷ a ∷ C₁))
          , (((wk↝ (proj₂ (get↝ v)) , undef) ∷ srel ∷ Srel , nn ∷ rrel ∷ Rrel)
          , call> (exprSim→ arg (srel ∷ Srel) (proj₂ (get↝ v)) eva))

cmdSim→ {P = P} (_∷_ {M = M} {c = c₁} srel Srel , _∷_ {C = C₁} {a = a} rrel Rrel)
        (c←> {d∈ = d∈} {v} {C} {c} {l = base ⋆ proof of off} {arg} {r} eva ret)
        = (((proj₁ (get↝ v) - undef) ∷ c₁ ∷ M)
          ⅋ FunDef.body (getDef P d∈) ∷ c ∷ C ⅋ (just ((base of off) , base) ∷ a ∷ C₁))
          , (((wk↝ (proj₂ (get↝ v)) , undef) ∷ srel ∷ Srel , (jj rfl ∷ rrel ∷ Rrel))
          , c←> (exprSim→ arg (srel ∷ Srel) (proj₂ (get↝ v)) eva) (exprSim→ r (srel ∷ Srel) poi ret))

⇌≡ : ∀ {L} {l l' : Maybe (Loc L)} {a : Maybe (Addr × ℕ)} → +M _⇌_ l a → +M _⇌_ l' a → l ≡ l'
⇌≡ nn nn = refl
⇌≡ (jj (rfl {n< = n<₁})) (jj (rfl {n< = n<})) rewrite leq n<₁ n<  = refl

|⇌|≡ : ∀ {L} {R R' : Ret L} {C : Cret L} → R |⇌| C → R' |⇌| C → R ≡ R'
|⇌|≡ [] [] = refl
|⇌|≡ (x ∷ r) (x' ∷ r') rewrite ⇌≡ x x' | |⇌|≡ r r' = refl

-- Backwards direction
cmdSim← : ∀ {X : Exports} {P : Prog X} {L₁ L₂ : StoreTy} {S₁ : State X L₁} {C₁ : CapState X L₁}
          {C₂ : CapState X L₂} → S₁ ∼ C₁ → P ⊩ C₁ ⟶ C₂ → ∃ λ S₂ → (S₂ ∼ C₂ × P ⊨ S₁ ⟶ S₂)
cmdSim← ([] , []) ()
cmdSim← (_∷_ {S = S} {p = p} srel Srel , _∷_ {R = R} {l = l} rrel Rrel) (ret> {c = c₁} {C₁})
        = ((p ∷ S) ↓ (c₁ ∷ C₁) ↓ (l ∷ R)) , ((srel ∷ Srel , rrel ∷ Rrel) , ret>)

cmdSim← (_∷_ {S = S} {p = p} srel Srel , _∷_ {R = R} {l = l} rrel Rrel) ($> ev) with
        cmdSim← (srel ∷ Srel , rrel ∷ Rrel) ev
cmdSim← (_∷_ {S = S} {p = p} srel Srel , _∷_ {R = R} {l = l} rrel Rrel) ($> ev) |
        .((_ ∷ _) ↓ (_ ∷ _) ↓ (_ ∷ _)) , ((sr ∷ Sr) , _∷_ rr Rr) , snd with ⇌≡ rrel rr | |⇌|≡ Rrel Rr
cmdSim← (_∷_ {S = S} {p = p} srel Srel , _∷_ {R = R} {l = l} rrel Rrel) ($> {c₂ = c₂} {c = c₄} {C₁} ev) |
        .((p₁ ∷ S₁) ↓ (c₂ ∷ C₁) ↓ (_ ∷ _)) , (_∷_ {S = S₁} {p = p₁} sr Sr , (rr ∷ Rr)) , snd | refl | refl
        = ((p₁ ∷ S₁) ↓ ((c₂ $ c₄) ∷ C₁) ↓ (l ∷ R)) , ((sr ∷ Sr , rr ∷ Rr) , ($> snd))

cmdSim← (_∷_ {S = S} {p = p} srel Srel , _∷_ {R = R} {l = l} rrel Rrel)
        (z> {c₂ = c₂} {C} {E} x) = ((p ∷ S) ↓ (c₂ ∷ C) ↓ (l ∷ R))
        , ((srel ∷ Srel , rrel ∷ Rrel) , (z> (exprSim← E (srel ∷ Srel) nat x)))

cmdSim← (_∷_ {S = S} {p = p} srel Srel , _∷_ {R = R} {l = l} rrel Rrel)
        (!z> {c₁ = c₁} {C = C} {E} x) = ((p ∷ S) ↓ (c₁ ∷ C) ↓ (l ∷ R))
        , ((srel ∷ Srel , rrel ∷ Rrel) , (!z> (exprSim← E (srel ∷ Srel) nat x)))

cmdSim← (_∷_ {S = S} {p = p} srel Srel , _∷_ {R = R} {l = l} rrel Rrel)
        (:=> {left = left} {right} {C} {a = base of off} {rev} lv rv a∈M safe) with evSane (srel ∷ Srel) lv
... | refl  = ((S.update (p ∷ S) (base ⋆ a∈M of off) (proj₁ rpair) up) ↓ (return unit ∷ C) ↓ (l ∷ R)) ,
              ((update|↝| (srel ∷ Srel) (proj₂ rpair)) , (rrel ∷ Rrel)) ,
                :=> {n< = a∈M} lsim rsim up
  where
  rpair = teg↝ rev (evValid (srel ∷ Srel) rv) (evSane (srel ∷ Srel) rv)
  up = safe↝Up {n< = a∈M} {off} safe (proj₂ rpair)
  lsim = exprSim← left (srel ∷ Srel) (poi {n< = a∈M}) lv
  rsim = exprSim← right (srel ∷ Srel) (proj₂ rpair) rv

cmdSim← (_∷_ {S = S} {p = p} srel Srel , _∷_ {R = R} nn Rrel) (endN> {C = cmds})
        = (S ↓ cmds ↓ R) , ((Srel , Rrel) , endN>)

cmdSim← (_∷_ {S = S} {p = p} srel Srel , _∷_ {R = R} {l = .(just (n ⋆ n< of b))}
        (jj (rfl {n} {n<} {b})) Rrel) (end←> {C = cmds} {e = e} {v = v} rv a∈M safe)
        with leq n< a∈M | evSane (srel ∷ Srel) rv
... | refl | san = (S.update S (n ⋆ a∈M of b) snv unv ↓ cmds ↓ R) ,
                   (update|↝| Srel (st↝ vrel) , Rrel) ,
                   end←> ((exprSim← e (srel ∷ Srel) vrel rv)) (safe↝Up safe vrel)
  where
  rpair = teg↝ v (evValid (srel ∷ Srel) rv) (evSane (srel ∷ Srel) rv)
  nv = proj₁ rpair
  vrel = proj₂ rpair
  stVp = strValUp (n ⋆ n< of b) nv (safe↝Up safe vrel)
  snv = proj₁ stVp
  unv = proj₂ stVp

cmdSim← {X} {P} (_∷_ {S = S} {p = p} srel Srel , _∷_ {R = R} {l = l} rrel Rrel)
        (call> {d∈ = d∈} {arg} {v} {C} {c₁} eva)
        = (((wkVal (proj₁ v↝c) (FunDef.ns def) - undef) ∷ p ∷ S)
          ↓ (FunDef.body def ∷ c₁ ∷ C) ↓ (nothing ∷ l ∷ R)) , (((wk↝ (proj₂ v↝c) , undef) ∷ srel ∷ Srel
          , (nn ∷ rrel ∷ Rrel)) , call> (exprSim← arg (srel ∷ Srel) (proj₂ v↝c) eva))
        where
        def = getDef P d∈
        v↝c = teg↝ v (evValid (srel ∷ Srel) eva) (evSane (srel ∷ Srel) eva)

cmdSim← {X} {P} (_∷_ {L} {Γ} {S} {M} {p} {c₁} srel Srel , _∷_ {R = R} {l = l} rrel Rrel)
        (c←> {d∈ = d∈} {arg} {r} {v} {C} {c} {a = base of off} {n} eva rl) with evSane (srel ∷ Srel) rl
... | refl = (((wkVal (proj₁ v↝c) (FunDef.ns def) - undef) ∷ p ∷ S) ↓
             (FunDef.body def ∷ c ∷ C) ↓ (just (base ⋆ rs of off) ∷ l ∷ R))
             , ((((wk↝ (proj₂ v↝c) , undef) ∷ srel ∷ Srel) , (jj rfl) ∷ rrel ∷ Rrel)
             , c←> inda indr)
  where
  def = getDef P d∈
  v↝c = teg↝ v (evValid (srel ∷ Srel) eva) (evSane (srel ∷ Srel) eva)
  rs = evValid (srel ∷ Srel) rl
  inda = exprSim← arg (srel ∷ Srel) (proj₂ v↝c) eva
  indr = exprSim← r (srel ∷ Srel) (poi {n< = rs}) rl
