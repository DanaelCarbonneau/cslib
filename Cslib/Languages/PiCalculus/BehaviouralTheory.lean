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

namespace Cslib.PiCal

section BehaviouralTheory

variable {Name : Type u} [DecidableEq Name]
  {defs : Constant → PiCal.Process Name → Prop}


open Process Act Act.Co

attribute [local grind] Tr

@[local grind]
private inductive ParNil : Process Name → Process Name → Prop where
| parNil : ParNil (p ‖ 𝐨ₘ) p


/-- P | 𝟎 ~ P -/
@[simp, scoped grind .]
theorem bisimilarity_par_nil [HasFresh Name] :
  (p ‖ 𝐨ₘ) ~[lts (Name := Name)] p :=
by
  exists ParNil
  constructor
  · have r := ParNil.parNil (p := p)
    assumption
  · intros s₁ s₂ hr μ
    cases hr
    constructor
    · intro s₁' htr
      cases htr
      case parL p' htr hinter =>
        exists p'
        apply And.intro htr ParNil.parNil
      repeat contradiction
    · intro s₂' htr
      exists (s₂' ‖ 𝐨ₘ)
      constructor
      · apply Tr.parL htr
        simp only [Process.fn,Motive.fn]
        exact Finset.inter_empty μ.bn
      · exact ParNil.parNil



/-- P ~ Q → (ν a) P ~ (ν a) Q -/
@[local grind]
private inductive ResBisim [HasFresh Name] :
  Process Name → Process Name → Prop where
| res : (p ~[lts (Name := Name)] q) → ResBisim (res a p) (res a q)
| remain :  (p ~[lts (Name := Name)] q)  → ResBisim p q

@[scoped grind .]
theorem bisimilarity_congr_res [HasFresh Name] :
    ∀a : Name, p ~[lts (Name := Name)] q →
    ((ν a) p) ~[lts (Name := Name)] ((ν a) q) := by
  intros a hbs
  exists ResBisim
  constructor
  · exact ResBisim.res hbs
  intros s₁ s₂ hr μ
  cases hr
  case res p' q' a hbs' =>
    constructor
    · intros s₁' htr
      cases htr
      case res a p'' hnontin htr =>
        obtain ⟨q'', htrq, hbs⟩ := Bisimilarity.is_bisimulation.follow_fst hbs' htr
        exists (ν a) q''
        apply And.intro (Tr.res htrq hnontin) (ResBisim.res hbs)
      case opn x htr=>
        obtain ⟨q'', htrq, hbs⟩ := Bisimilarity.is_bisimulation.follow_fst hbs' htr
        exists q''
        apply And.intro ( Tr.opn htrq) (ResBisim.remain hbs)
    · intros s₂' htr
      cases htr
      case res q'' hnotin htr =>
        obtain ⟨p'',htrp,hbs⟩ := Bisimilarity.is_bisimulation.follow_snd hbs' htr
        exists (ν a) p''
        apply And.intro (Tr.res htrp hnotin) (ResBisim.res hbs)
      case opn x htr =>
        obtain ⟨p'',htrp,hbs⟩ := Bisimilarity.is_bisimulation.follow_snd hbs' htr
        exists p''
        apply And.intro ( Tr.opn htrp) (ResBisim.remain hbs)
  case remain hbs =>
    constructor
    · intro s₁' htr
      obtain ⟨s₂', htr₂, hbs⟩ := Bisimilarity.is_bisimulation.follow_fst hbs htr
      exact ⟨s₂', (And.intro htr₂ (ResBisim.remain hbs))⟩
    · intro s₂' htr
      obtain ⟨s₁',htr₁,hbs⟩ :=  Bisimilarity.is_bisimulation.follow_snd hbs htr
      exact ⟨s₁', (And.intro htr₁ (ResBisim.remain hbs))⟩

end BehaviouralTheory
end Cslib.PiCal
