/-
Copyright (c) 2025 Danaël Carbonneau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Danaël Carbonneau, Fabrizio Montesi
-/

import Cslib.Languages.PiCalculus.Semantics

namespace CslibTests

open Cslib.PiCal
open Process

variable {Name : Type u} [DecidableEq Name] {Constant : Type v}
  {defs : Constant → Process Name Constant → Prop}


def pEx (a b x y : Name) : Process Name Constant := -- a(x).x'⟨y⟩ | a'⟨b⟩.nil
  par (pre (Chan.recv a x) (pre (Chan.send x y) nil )) (pre (Chan.send a b) nil)
def pEx' (a b x y : Name) : Process Name Constant :=
  (a(x)·x-⟨y⟩·∘ )‖(a-⟨b⟩·∘ )

example (a b x y : Name) : (pEx a b x y (Constant := Constant))= pEx' a b x y :=
by
  unfold pEx pEx'
  rfl

#eval (pre (Chan.recv 1 2) (pre (Chan.send 2 3) nil ) (Constant := ℕ)).subst  2 4


#eval (pEx 1 2 3 4  (Constant := Nat))[4 :=5]



#check (· +1)

-- #check DecidableEq ℕ
-- #check instDecidableEqNat

-- def p : Process ℕ ℕ := (pre (Chan.recv 1 2) (pre (Chan.send 2 3) nil))
-- #check @Tr
-- @[lts ltsNat "ₙ"]
-- def TrNat := @Tr ℕ ℕ instDecidableEqNat


-- example : p [Act.name 1 4]⭢ₙ (pre (Chan.send 4 3) nil) :=
--   by
--     sorry





def P : Process String String := pre (Chan.recv "a" "x") (pre (Chan.send "x" "y") nil)

def P' : Process String String :=  "a"("x")·"x"-⟨"y"⟩·∘

example : P = P' := rfl



example : Tr P (Act.name "a" "b") (pre (Chan.send "b" "y") nil) :=
by
  apply Tr.inp





#check pEx


-- example [DecidableEq Name] [HasFresh Name]
--   (a b x y : Name) (hneq : y ≠ x)
--   : Tr (pEx a b x y) (Act.τ) ((pre (Chan.send b y) nil).par nil) (Constant := Constant)
--   :=
-- by
--   unfold pEx
--   apply Tr.com (μ := Act.name a b) (μ' := Act.coname a b)
--   · exact Act.Co.nc
--   · have h := Tr.inp (a := a) (v := b) (x := x) (p := pre (Chan.send x y) nil)
--       (Constant := Constant)
--     simp only [HasSubstitution.subst,Process.subst] at h
--     simp only [ite_self] at h
--     simp only [Chan.subst,reduceIte] at h
--     split at h
--     case a.isTrue ht =>
--       contradiction -- On évite ce cas car pour l'instant ça déconne !
--     case a.isFalse hf =>
--       exact h
--   · exact Tr.out



-- def P1 (a b : Act Name) : Process Name Constant :=
--   Process.choice (Process.pre a (Process.pre b Process.nil))
--   (Process.pre b (Process.pre a Process.nil))


-- example (a b : Act Name) :
--   Tr (P1 a b) a (Process.pre b Process.nil) (defs := defs):=
-- by
--   constructor
--   exact Tr.pre

-- -- a | a'
-- def P2 (a : Name) : Process Name Constant :=
--   Process.par (Process.pre (Act.name a) Process.nil) (Process.pre (Act.coname a) Process.nil)


-- example (a : Name) :
--   Tr (P2 a) Act.τ (Process.nil.par Process.nil) (defs := defs):=
-- by
--   simp only [P2]
--   apply Tr.com (p := (pre (Act.name a) nil)) (q := pre (Act.coname a) nil) (p' := nil) (q' := nil)
--     (μ := Act.name a) (μ' := Act.coname a)
--   · exact Act.Co.nc
--   · exact Tr.pre
--   · exact Tr.pre


-- def P3 : Process String Constant :=
--   Process.par (Process.pre (Act.name "a") Process.nil) (Process.pre (Act.coname "a") Process.nil)


-- -- Exemple avec bang

-- def P4 (a b : Name) : Process Name Constant := -- !a.b'.0 | a'.b.0
--   (bang (name a) (pre (coname b) nil)).par (pre (coname a) (pre (name b) nil))

-- def P4' (a b : Name) : Process Name Constant := -- !a.b'.0 | b'.0 | b.0
--   ((bang (name a) (pre (coname b) nil)).par (pre (coname b) nil)).par
--     (pre (name b) nil)

-- def P4'' (a b : Name) : Process Name Constant := -- !a.b'.0 | 0 | 0
--   ((bang (name a) (pre (coname b) nil)).par nil).par nil

-- #check Tr.pre

-- example {a b : Name} :
--   Tr (P4 a b) τ (P4' a b) (defs := defs) ∧ Tr (P4' a b) τ (P4'' a b) (defs := defs)
-- :=
-- by
--   simp only [P4',P4'']
--   constructor
--   · apply Tr.com (μ := name a) (μ' := coname a)
--     · exact Co.nc
--     · exact Tr.repl
--     · exact Tr.pre
--   · apply Tr.com (μ := coname b) (μ' := name b)
--       (p := (((bang (name a) (pre (coname b) nil)).par (pre (coname b) nil))))
--       (q := (pre (name b) nil))
--       (p' := (((bang (name a) (pre (coname b) nil)).par nil)))
--       (q' := nil)
--     · exact Co.cn
--     · apply Tr.parR
--       exact Tr.pre
--     · exact Tr.pre

end CslibTests
