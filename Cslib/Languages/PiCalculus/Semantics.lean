/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Languages.PiCalculus.Basic

@[expose] public section

/-! # Semantics of PiCal

## Main definitions
- `PiCal.Tr`: transition relation for PiCal.
- `PiCal.lts`: the `LTS` of PiCal.

-/

namespace Cslib

variable
  {Name : Type u}
  {Constant : Type v}
  {defs : Constant → (PiCal.Process Name Constant) → Prop}

namespace PiCal

open Process





/-- The transition relation for PiCal.  -/
@[lts PiCal.lts]
inductive Tr [DecidableEq Name] [HasFresh Name] : Process Name Constant → Act Name → Process Name Constant → Prop
where
  | parL : Tr p μ p' → Tr (p ‖ q) μ (p' ‖ q)
  | parR : Tr q μ q' → Tr (p ‖ q) μ (p ‖ q')
  | choiceL : Tr p μ p' → Tr (p + q) μ p'
  | choiceR : Tr q μ q' → Tr (p + q) μ q'
  | com :
    μ.Co μ' → Tr p μ p' → Tr q μ' q' → Tr (p ‖ q) Act.τ (p' ‖ q')
  | out : Tr (a-⟨x⟩·p) (Act.coname a x) p
  | inp : Tr (a(x)·p) (Act.name a v) (p[x := v])
  | res : a ∉ μ → Tr p μ p' →  Tr ((ν a) p) μ ( (ν a) p')
  | opn : Tr p (Act.coname a b) p' → Tr ((ν b) p) (Act.coname_open a b) p'

  | clsL : Tr p (Act.name a b) p' → Tr q (Act.coname_open a b) q' →
    Tr (p ‖ q) τ (res b (p' ‖ q'))
  | clsR : Tr p (Act.coname_open a b) p' → Tr q (Act.name a b) q' →
    Tr (p ‖ q) τ (res b (p' ‖ q'))

  | rpl : Tr (bang a x p) (Act.name a v) ((bang a x p) ‖  (p[x := v]))

  -- | res : μ ≠ Act.name a → μ ≠ Act.coname a → Tr p μ p' → Tr (res a p) μ (res a p')
  -- | const : defs k p → Tr p μ p' → Tr (const k) μ p'
  -- | repl : Tr (bang a p) a ((bang a p).par p)


def P : Process String String := pre (Chan.recv "a" "x") (pre (Chan.send "x" "y") nil)

def P' : Process String String :=  "a"("x")·"x"-⟨"y"⟩·∘

example : P = P' := rfl



example : Tr P (Act.name "a" "b") (pre (Chan.send "b" "y") nil) :=
by
  apply Tr.inp





#check pEx


example [DecidableEq Name] [HasFresh Name]
  (a b x y : Name) (hneq : y ≠ x)
  : Tr (pEx a b x y) (Act.τ) ((pre (Chan.send b y) nil).par nil) (Constant := Constant)
  :=
by
  unfold pEx
  apply Tr.com (μ := Act.name a b) (μ' := Act.coname a b)
  · exact Act.Co.nc
  · have h := Tr.inp (a := a) (v := b) (x := x) (p := pre (Chan.send x y) nil)
      (Constant := Constant)
    simp only [HasSubstitution.subst,Process.subst] at h
    simp only [ite_self] at h
    simp only [Chan.subst,reduceIte] at h
    split at h
    case a.isTrue ht =>
      contradiction -- On évite ce cas car pour l'instant ça déconne !
    case a.isFalse hf =>
      exact h
  · exact Tr.out





instance : HasTau (Act Name) where
  τ := Act.τ


open Process
open Act
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

end PiCal


end Cslib
