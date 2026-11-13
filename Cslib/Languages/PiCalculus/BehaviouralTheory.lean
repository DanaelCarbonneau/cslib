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

open LTS

open Process Act Act.Co Motive

attribute [local grind] Tr

@[local grind]
private inductive ParNil : Process Name → Process Name → Prop where
| parNil : ParNil (p ‖ 𝐨ₘ) p


/-- P | 𝟎 ~ P -/
@[simp, scoped grind .]
theorem bisimilarity_par_nil [HasFresh Name] (p : Process Name):
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

#check Bisimilarity

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
        obtain ⟨q'', htrq, hbs⟩ := Bisimilarity.follow_fst hbs' htr
        exists (ν a) q''
        apply And.intro (Tr.res htrq hnontin) (ResBisim.res hbs)
      case opn x htr=>
        obtain ⟨q'', htrq, hbs⟩ := Bisimilarity.follow_fst hbs' htr
        exists q''
        apply And.intro ( Tr.opn htrq) (ResBisim.remain hbs)
    · intros s₂' htr
      cases htr
      case res q'' hnotin htr =>
        obtain ⟨p'',htrp,hbs⟩ := Bisimilarity.follow_snd hbs' htr
        exists (ν a) p''
        apply And.intro (Tr.res htrp hnotin) (ResBisim.res hbs)
      case opn x htr =>
        obtain ⟨p'',htrp,hbs⟩ := Bisimilarity.follow_snd hbs' htr
        exists p''
        apply And.intro ( Tr.opn htrp) (ResBisim.remain hbs)
  case remain hbs =>
    constructor
    · intro s₁' htr
      obtain ⟨s₂', htr₂, hbs⟩ := Bisimilarity.follow_fst hbs htr
      exact ⟨s₂', (And.intro htr₂ (ResBisim.remain hbs))⟩
    · intro s₂' htr
      obtain ⟨s₁',htr₁,hbs⟩ :=  Bisimilarity.follow_snd hbs htr
      exact ⟨s₁', (And.intro htr₁ (ResBisim.remain hbs))⟩


@[local grind]
private inductive ParComm : Process Name → Process Name → Prop where
| parComm : ParComm (par p q) (par q p)
-- TODO : find a way to deal with ν appearing after the close transition

/-- P | Q ~ Q | P -/
@[scoped grind .]
theorem bisimilarity_par_comm [HasFresh Name] : (par p q) ~[lts (Name := Name)] (par q p)
:= by
  let defParComm : Process Name  → Process Name
    | par p q => par q p
    | _ => motive nil
  use ParComm, ParComm.parComm
  intros s₁ s₂ hpc μ
  unfold lts at *
  split_ands
  · intro s₁' htr
    induction hpc
    case parComm =>
      cases htr
      case parL p q p' htr hn =>
        exists (q ‖ p')
        apply And.intro (Tr.parR htr hn) ParComm.parComm
      case parR p q q' hn htr =>
        exists (q'‖ p)
        apply And.intro (Tr.parL htr hn) ParComm.parComm
      case comm p q μ p' μ' q' hco htr₁ htr₂ =>
        exists (q' ‖ p')
        apply And.intro (Tr.comm htr₂ htr₁ (Co.symm hco)) ParComm.parComm
      case closeL p q x z p' q' htr₁ htr₂ hn =>
        exists (ν z) (q'‖ p')
        constructor
        · apply Tr.closeR htr₂ htr₁ hn
        · sorry
      case closeR p q x z p' q' htr₁ hn htr₂  =>
        exists (ν z) (q' ‖ p')
        constructor
        · apply Tr.closeL htr₂ htr₁ hn
        sorry
  · sorry


-- private inductive NotFreeRes : Process Name → Process Name → Prop where
--   | not_free : z∉ P.fn → NotFreeRes P ((ν z) P)
-- theorem bisimilarity_not_free_res [HasFresh Name] : z ∉ P.fn → P ~[lts (Name := Name)] ((ν z) P)
-- := by -- pas sûr que ce soit vrai...
--   intro hnotin
--   use NotFreeRes, NotFreeRes.not_free hnotin
--   intros s₁ s₂ hr μ
--   constructor
--   · intro s₁' htr
--     cases hr
--     case not_free z hn =>

--       sorry
--   · intro s₂' htr
--     cases hr
--     case not_free z hn =>
--       cases htr
--       case res p' hn' htr=>
--         exists p'
--         use htr
--         apply NotFreeRes.not_free
--         intro hf
--         -- il faudrait un théorème sur la présence de noms
--         sorry
--       case opn x htr =>
--         -- il faudrait un théorème sur le fait que si z n'est pas libre dans s₁, on ne peut pas
--         -- l'envoyer ?

--         sorry


@[local grind]
private inductive ParAssoc : Process Name  → Process Name  → Prop where
  | assoc : ParAssoc (par p (par q r)) (par (par p q) r)
  | id : ParAssoc p p
--  might need more cases to cover ν
/-- P | (Q | R) ~ (P | Q) | R -/
theorem bisimilarity_par_assoc [HasFresh Name]:
  (par p (par q r)) ~[lts (Name := Name)] (par (par p q) r) := by
  use ParAssoc, ParAssoc.assoc
  intros s₁ s₂ hr μ
  constructor
  · intro s₁' htr
    cases hr
    case assoc p q r =>
      cases htr
      case parL => sorry
      case parR => sorry
      case comm => sorry
      case closeL x z p' qr' htr₁ htr₂ hn =>
        cases htr₂
        case parL q' htr' hinter =>

          sorry
        case parR => sorry
      case closeR => sorry
    case id p => sorry
  sorry


private inductive ChoiceNil : Process Name  → Process Name  → Prop where
  | nil : ChoiceNil ((p + 𝐨)ₘ) p
  | id : ChoiceNil p p

/-- P + 𝟎 ~ P -/
theorem bisimilarity_choice_nil [HasFresh Name]: ((p + 𝐨)ₘ) ~[lts (Name := Name)] p := by
  use ChoiceNil, ChoiceNil.nil
  intros s₁ s₂ hr μ
  constructor
  · intro s₁' htr
    cases hr
    case nil p =>
      cases htr
      case sumL htr' =>
        exists s₁'
        exact And.intro htr' (ChoiceNil.id)
      case sumR q' htr' =>
        cases htr'
    case id =>
      exists s₁'
      apply And.intro htr ChoiceNil.id
  · intro s₂' htr
    cases hr
    case nil p =>
      exists s₂'
      apply And.intro (Tr.sumL htr) ChoiceNil.id
    case id =>
      exists s₂'
      apply And.intro htr ChoiceNil.id


@[local grind]
private inductive ChoiceIdem : Process Name  → Process Name  → Prop where
  | idem : ChoiceIdem (sum p p) (motive p)
  | id : ChoiceIdem p p

/-- P + P ~ P -/
theorem bisimilarity_choice_idem [HasFresh Name]:
  (sum p p) ~[lts (Name := Name)] (motive p) := by
  use ChoiceIdem, ChoiceIdem.idem
  intros s₁ s₂ hr μ
  constructor
  · intro s₁' htr
    cases hr
    case idem p =>
      cases htr
      case sumL p' htr | sumR p' htr => exact ⟨s₁',(And.intro htr ChoiceIdem.id)⟩
    case id p => exact ⟨s₁',⟨htr,ChoiceIdem.id⟩⟩
  · intro s₂' htr
    cases hr
    case idem p => exact ⟨s₂',⟨Tr.sumL htr,ChoiceIdem.id⟩⟩
    case id p => exact ⟨s₂',⟨htr,ChoiceIdem.id⟩⟩



private inductive ChoiceComm [HasFresh Name] : Process Name → Process Name → Prop where
  | choiceComm : ChoiceComm (sum p q) ((sum q p)ₘ)
  | bisim : (p ~[lts (Name := Name)] q) → ChoiceComm p q

open Bisimilarity LTS in
/-- P + Q ~ Q + P -/
theorem bisimilarity_choice_comm [HasFresh Name]:
  (sum p q) ~[lts (Name := Name)] ((sum q p)ₘ) := by
  use ChoiceComm, ChoiceComm.choiceComm
  intros s₁ s₂ hr μ
  constructor
  case _ =>
    intro s₁' htr
    cases hr
    case choiceComm p q =>
      exists s₁'
      constructor
      · cases htr
        case sumL htr => exact Tr.sumR htr
        case sumR htr => exact Tr.sumL htr
      · apply ChoiceComm.bisim
        exact HomBisimilarity.refl s₁'
    case bisim hbs =>
      have ⟨s₂',h⟩ := Bisimilarity.follow_fst hbs htr
      exists s₂'
      apply And.intro h.1
      exact ChoiceComm.bisim h.2
  case _ =>
    intro s₂' htr
    cases hr
    case choiceComm p q =>
      exists s₂'
      constructor
      · cases htr
        case sumL htr => exact Tr.sumR htr
        case sumR htr => exact Tr.sumL htr
      · exact ChoiceComm.bisim (HomBisimilarity.refl s₂' )

    case bisim hbs =>
      have ⟨s₁',h⟩ := Bisimilarity.follow_snd hbs htr
      exists s₁'
      exact And.intro h.1 (ChoiceComm.bisim h.2)


private inductive ChoiceAssoc : Process Name → Process Name → Prop where
  | assoc : ChoiceAssoc (sum p (sum q r)) ((sum (sum p q) r)ₘ)
  | id : ChoiceAssoc p p

/-- P + (Q + R) ~ (P + Q) + R -/
theorem bisimilarity_choice_assoc [HasFresh Name] :
    (sum p (sum q r)) ~[lts (Name := Name)] ((sum (sum p q) r)ₘ) := by
  use ChoiceAssoc, ChoiceAssoc.assoc
  intros s₁ s₂ hr μ
  constructor <;> cases hr
  case left.assoc p q r =>
    intro s htr
    refine ⟨s, ?_, ChoiceAssoc.id⟩
    cases htr
    case sumL htr => apply Tr.sumL; apply Tr.sumL; assumption
    case sumR htr =>
      cases htr
      case sumL htr => apply Tr.sumL; apply Tr.sumR; assumption
      case sumR htr => apply Tr.sumR; assumption
  case right.assoc p q r =>
    intro s htr
    refine ⟨s, ?_, ChoiceAssoc.id⟩
    cases htr
    case sumL htr =>
      cases htr
      case sumL htr => apply Tr.sumL; assumption
      case sumR htr => apply Tr.sumR; apply Tr.sumL; assumption
    case sumR htr => apply Tr.sumR; apply Tr.sumR; assumption
  all_goals grind [ChoiceAssoc.id]


@[local grind]
private inductive SubstBisim [HasFresh Name] : Process Name → Process Name → Prop where
| subst {x y : Name} : (p ~[lts (Name := Name)] q) → SubstBisim (p[x :=y]) (q[x:=y])

theorem Bisim_subst [HasFresh Name] (p q : Process Name) (b z : Name) :
  (p ~[lts (Name := Name)] q) → (p[b:=z]) ~[lts (Name := Name)] (q[b:=z]) := by
  intro hbis
  use SubstBisim
  constructor
  · exact SubstBisim.subst hbis
  intro s₁ s₂ hr μ
  constructor
  · intro s₁' htr
    cases hr
-- On a clairement pas encore les bons outils pour ça...


    sorry
  · sorry

@[local grind]
private inductive PreBisim [HasFresh Name] : Process Name  → Process Name  → Prop where
| pre : (p ~[lts (Name := Name)] q) → PreBisim (pre μ p) (pre μ q)
| bisim : (p ~[lts (Name := Name)] q) → PreBisim p q
-- TODO : gérer les gardes !!!
open scoped LTS in
/-- P ~ Q → μ.P ~ μ.Q -/
theorem bisimilarity_congr_pre [HasFresh Name] :
  (p ~[lts (Name := Name)] q) → (pre μ p) ~[lts (Name := Name)] (pre μ q) := by
  intro hpq
  use PreBisim
  constructor
  · exact PreBisim.pre hpq
  intro s1 s2 hr μ'
  cases hr
  case pre p' q' μ hbis =>
    constructor
    · intro s₁ htr
      induction μ
      case send a b =>
        cases htr
        exact ⟨q',Tr.out, PreBisim.bisim hbis⟩
      case recv a b =>
        cases htr
        expose_names
        exists q'[b:=z]
        apply And.intro Tr.inp
        apply PreBisim.bisim

        sorry
      case guard x y π π_ih =>
        cases htr
        case mat htr =>
          specialize π_ih htr
          have ⟨s₂',htr,hr⟩ := π_ih
          exact ⟨s₂',Tr.mat htr,hr⟩
      case τ =>
        cases htr
        exact  ⟨q',Tr.tau,PreBisim.bisim hbis⟩
    · intro s₂ htr
      induction μ
      case send a b =>
        cases htr
        exact ⟨p',Tr.out,PreBisim.bisim hbis⟩
      case recv a b =>
        cases htr
        expose_names
        exists p'[b:=z]
        apply And.intro Tr.inp
        apply PreBisim.bisim
        sorry
      case guard x y π π_ih =>
        cases htr
        case mat htr =>
          specialize π_ih htr
          have ⟨s₂',htr,hr⟩ := π_ih
          exact ⟨s₂',Tr.mat htr,hr⟩
      case τ =>
        cases htr
        exact ⟨p',Tr.tau,PreBisim.bisim hbis⟩

  case bisim =>

    sorry
    --grind [Bisimilarity.largest_bisimulation]
#check Tr.inp
end BehaviouralTheory
end Cslib.PiCal
