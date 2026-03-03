/-
Copyright (c) 2026 Danaël Carbonneau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Danaël Carbonneau, Fabrizio Montesi
-/
module

public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Cslib.Languages.PiCalculus.Semantics

@[expose] public section

/-! # Behavioural theory of Pi Calculus

## Main results


-/

namespace Cslib

section PiCal.BehaviouralTheory

variable {Name : Type u} [DecidableEq Name] {Constant : Type v}
  {defs : Constant → PiCal.Process Name Constant → Prop}

namespace PiCal

open Process Act Act.Co

attribute [local grind] Tr

@[local grind]
private inductive ParNil : Process Name Constant → Process Name Constant → Prop where
| parNil : ParNil (p ‖ ∘) p


/-- P | 𝟎 ~ P -/
@[simp, scoped grind .]
theorem bisimilarity_par_nil [HasFresh Name] :
  (p ‖ ∘) ~[lts (Name := Name) (Constant := Constant)] p :=
  by
    exists ParNil
    constructor
    · exact ParNil.parNil
    intros s₁ s₂ hr μ
    cases hr
    constructor
    · intro s' htr
      cases htr
      case parL p' htr =>
        exists p'
        exact And.intro htr ParNil.parNil
      repeat contradiction
    · intro s2' htr
      exists par s2' nil
      exact And.intro (Tr.parL htr) (ParNil.parNil)

@[local grind]
private inductive ResBisim [HasFresh Name] :
  Process Name Constant → Process Name Constant → Prop where
| res : (p ~[lts (Name := Name)] q) → ResBisim (res a p) (res a q)
| remain :  (p ~[lts (Name := Name)] q)  → ResBisim p q

/-- P ~ Q → (ν a) P ~ (ν a) Q
-/
@[scoped grind .]
theorem bisimilarity_congr_res [HasFresh Name] :
    ∀a : Name, p ~[lts (Name := Name)] q →
    ((ν a) p) ~[lts (Name := Name)] ((ν a) q) := by
  intros a hbisim
  exists ResBisim
  constructor
  · exact ResBisim.res hbisim
  intros s₁ s₂ hr μ
  cases hr
  case res =>
    rename_i p q a h
    constructor
    case left =>
      intro s₁' htr
      cases htr
      case res p' hnotin htr =>
        obtain ⟨q', htrq, hbs⟩ := Bisimilarity.is_bisimulation.follow_fst h htr
        exists res a q'
        unfold lts at *
        have h := (Tr.res hnotin htrq )
        exact And.intro h (ResBisim.res hbs)
      case opn a' htr =>
        obtain ⟨q', htrq, hbs⟩ := Bisimilarity.is_bisimulation.follow_fst h htr
        exists q'
        exact And.intro (Tr.opn htrq) (ResBisim.remain hbs)
    case right =>
      intro s₂' htr
      cases htr
      case res p hnotin htr =>
        obtain ⟨q', htrq, hbs⟩ := Bisimilarity.is_bisimulation.follow_snd h htr
        exists res a q'
        unfold lts at *
        have h := (Tr.res hnotin htrq )
        exact And.intro h (ResBisim.res hbs)
      case opn a' htr =>
        obtain ⟨q', htrq, hbs⟩ := Bisimilarity.is_bisimulation.follow_snd h htr
        exists q'
        exact And.intro (Tr.opn htrq) (ResBisim.remain hbs)
  case remain hbs =>
    constructor
    · intro s₁' htr
      obtain ⟨s₂', htr₂, hbs⟩ := Bisimilarity.is_bisimulation.follow_fst hbs htr
      exists s₂'
      apply And.intro htr₂ (ResBisim.remain hbs)
    · intro s₂' htr
      obtain ⟨s₁',htr₁, hbs⟩ := Bisimilarity.is_bisimulation.follow_snd hbs htr
      exists s₁'
      apply And.intro htr₁ (ResBisim.remain hbs)


-- @[local grind]
-- private inductive ParComm : Process Name Constant → Process Name Constant → Prop where
-- | parComm : ParComm (par p q) (par q p)
-- | parCommRes : ParComm ((νb)p‖q) ((νb)q‖p)
-- /-- P | Q ~ Q | P -/
-- @[scoped grind .]
-- theorem bisimilarity_par_comm  [HasFresh Name] :
--   (par p q) ~[lts (Name := Name) (Constant := Constant)] (par q p) := by
--   let defParComm : Process Name Constant → Process Name Constant
--     | par p q => par q p
--     | _ => nil
--   use ParComm, ParComm.parComm
--   intro s₁ s₂ hr μ
--   unfold lts at *
--   constructor
--   · intro s₁' htr
--     cases hr
--     case right.left.parComm p' q' =>
--       cases htr
--       case parL p'' htr =>
--         exists (q' ‖ p'')
--         grind
--       case parR q'' htr =>
--         exists (q'' ‖ p')
--         grind
--       case com μ μ'  hco p'' q'' htr₁ htr₂ =>
--         exists (par q'' p'')
--         grind
--       case clsL a b p'' q'' htr₁ htr₂ =>
--         exists ((ν b) q'' ‖ p'')
--         constructor
--         · exact Tr.clsR htr₂ htr₁
--         · exact ParComm.parCommRes
--       case clsR a b p'' q'' htr₁ htr₂ =>
--         exists ((ν b) q'' ‖ p'')
--         constructor
--         · exact Tr.clsL htr₂ htr₁
--         · exact ParComm.parCommRes
--     case right.left.parCommRes a p' q' =>
--       cases htr
--       case res p'' hnotin htr =>
--         cases htr
--         case parL p'' htr =>
--           exists (ν a) q' ‖ p''
--           apply And.intro (Tr.res hnotin (Tr.parR htr)) ParComm.parCommRes
--         case parR q'' htr =>
--           exists (ν a) q'' ‖ p'
--           apply And.intro (Tr.res hnotin (Tr.parL htr)) ParComm.parCommRes
--         case com μ μ' hco p'' q'' htr₁ htr₂ =>
--           exists (ν a) q'' ‖ p''
--           apply And.intro (Tr.res hnotin (Tr.com hco.symm htr₂ htr₁)) ParComm.parCommRes
--         case clsL b c p'' q'' htr₁ htr₂ =>
--           -- PROBLÈME : relation trop précise, n'est pas vraie
--           sorry
--         repeat sorry
--       case opn =>
--       sorry
--   · sorry





@[local grind]
private inductive ParComm : Process Name Constant → Process Name Constant → Prop where
| parComm : ParComm (par p q) (par q p)
| parCommRes : ParComm p q → ParComm ((ν a) p) ((ν a) q)
/-- P | Q ~ Q | P -/
@[scoped grind .]
theorem bisimilarity_par_comm  [HasFresh Name] :
  (par p q) ~[lts (Name := Name) (Constant := Constant)] (par q p) := by
  let defParComm : Process Name Constant → Process Name Constant
    | par p q => par q p
    | _ => nil
  use ParComm, ParComm.parComm
  intro s₁ s₂ hr μ
  unfold lts at *
  constructor
  · intro s₁' htr
    cases hr
    case right.left.parComm p' q' =>
      cases htr
      case parL p'' htr =>
        exists (q' ‖ p'')
        grind
      case parR q'' htr =>
        exists (q'' ‖ p')
        grind
      case com μ μ'  hco p'' q'' htr₁ htr₂ =>
        exists (par q'' p'')
        grind
      case clsL a b p'' q'' htr₁ htr₂ =>
        exists ((ν b) q'' ‖ p'')
        constructor
        · exact Tr.clsR htr₂ htr₁
        · apply ParComm.parCommRes
          sorry
      case clsR a b p'' q'' htr₁ htr₂ =>
        exists ((ν b) q'' ‖ p'')
        constructor
        · exact Tr.clsL htr₂ htr₁
        · sorry
    case right.left.parCommRes p' q' a => sorry
  · sorry




end PiCal

end PiCal.BehaviouralTheory

end Cslib
