/-
Copyright (c) 2026 Danaël Carbonneau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Danaël Carbonneau
-/

import Cslib.Languages.PiCalculus.Semantics
import Cslib.Languages.PiCalculus.BehaviouralTheory

namespace CslibTests

open Cslib

open PiCal Process



open Process Prefix Motive
/-- #Examples of Process. -/
def P₁ := 1(2)∘(2⟨3⟩∘𝐨ₘ ‖ 2⟨4⟩∘𝐨ₘ)
def P₂ :=  (("z"⟨"y"⟩∘ 𝐨ₘ) + "w"("v")∘𝐨ₘ) ‖ ("x"⟨"u"⟩∘𝐨ₘ)ₘ
def P₃ := (ν "x") ((("x"("z")∘"z"⟨"y"⟩∘𝐨ₘ) + ("w"⟨"v"⟩∘𝐨ₘ )) ‖ (ν "u") "x"⟨"u"⟩∘𝐨ₘ)
def P₄ :=
  (ν "z") ((["x" = "x"]("x"⟨"z"⟩))∘𝐨ₘ) ‖ ((ν "w") (("w"⟨"a"⟩∘𝐨ₘ)) ‖ (("w"("v")∘𝐨ₘ)+("y"("u")∘𝐨ₘ)))



section Names


/- Prefix bound and free names-/
example :  (Prefix.guard 1 2 (Prefix.recv 1 2)).n = {1,2} := rfl

example : (Prefix.guard 1 2 (Prefix.recv 1 2)).bn = {2} := rfl

example :  (Prefix.guard 1 2 (Prefix.recv 1 3)).fn = {1,2} :=
by
  repeat unfold Prefix.fn
  exact Finset.union_singleton 1 {1, 2}

/-- Process free names -/
example : P₁.fn = {1,3,4} := rfl
example : P₂.fn = {"z","y","w","x","u"} := rfl
example : P₃.fn = {"y","w","v"} := rfl

/-- Process bound names -/
example : P₁.bn = {2} := rfl
example : P₂.bn = {"v"} := rfl
example : P₃.bn = {"x","z","u"} :=
  Finset.union_singleton "x" ({"z"} ∪ (∅ ∪ ∅) ∪ (∅ ∪ ∅) ∪ (∅ ∪ ∅ ∪ {"u"}))


end Names


section AlphaEquiv


example : AlphaEquiv (("a"("y")∘ "y"⟨"z"⟩∘ 𝐨ₘ)ₘ)  (("a"("y")∘ "y"⟨"z"⟩∘ 𝐨ₘ)ₘ) :=
by
  exact AlphaEquiv.refl

example : AlphaEquiv
  ((ν "y") (("y"("z")∘ "z"⟨"x"⟩∘𝐨ₘ)‖ (ν "w") ("y"⟨"w"⟩∘"w"("v")∘"x"⟨"v"⟩∘𝐨ₘ)))
  ((ν "u") (("u"("y")∘ "y"⟨"x"⟩∘𝐨ₘ)‖ (ν "w") ("u"⟨"w"⟩∘"w"("z")∘"x"⟨"z"⟩∘𝐨ₘ)))
:= by
  have h₁ : AlphaEquiv ((ν "y") (("y"("z")∘ "z"⟨"x"⟩∘𝐨ₘ)‖ (ν "w") ("y"⟨"w"⟩∘"w"("v")∘"x"⟨"v"⟩∘𝐨ₘ)))
                      ((ν "u") (("u"("z")∘ "z"⟨"x"⟩∘𝐨ₘ)‖ (ν "w") ("u"⟨"w"⟩∘"w"("v")∘"x"⟨"v"⟩∘𝐨ₘ)))
  := by
    apply AlphaEquiv.cbn
    apply ChangeBoundName.res
    simp only [Process.fn,Motive.fn,Prefix.fn,Prefix.bn]
    exact Finset.erase_eq_self.mp rfl
  have h₂ : AlphaEquiv
    ((ν "u") (("u"("z")∘ "z"⟨"x"⟩∘𝐨ₘ)‖ (ν "w") ("u"⟨"w"⟩∘"w"("v")∘"x"⟨"v"⟩∘𝐨ₘ)))
    ((ν "u") (("u"("y")∘ "y"⟨"x"⟩∘𝐨ₘ)‖ (ν "w") ("u"⟨"w"⟩∘"w"("v")∘"x"⟨"v"⟩∘𝐨ₘ)))
  := by
    apply AlphaEquiv.cbn
    apply ChangeBoundName.res_traverse
    apply ChangeBoundName.par_traverseL
    apply ChangeBoundName.inp
    simp only [Process.fn,Motive.fn,Prefix.fn,Prefix.bn]
    exact Finset.erase_eq_self.mp rfl
  have h₃ : AlphaEquiv
    ((ν "u") (("u"("y")∘ "y"⟨"x"⟩∘𝐨ₘ)‖ (ν "w") ("u"⟨"w"⟩∘"w"("v")∘"x"⟨"v"⟩∘𝐨ₘ)))
    ((ν "u") (("u"("y")∘ "y"⟨"x"⟩∘𝐨ₘ)‖ (ν "w") ("u"⟨"w"⟩∘"w"("z")∘"x"⟨"z"⟩∘𝐨ₘ)))
  := by
    apply AlphaEquiv.cbn
    apply ChangeBoundName.res_traverse
    apply ChangeBoundName.par_traverseR
    apply ChangeBoundName.res_traverse
    apply ChangeBoundName.prefix_traverse
    apply ChangeBoundName.inp
    simp only [Process.fn,Motive.fn,Prefix.fn,Prefix.bn]
    exact Finset.erase_eq_self.mp rfl
  exact AlphaEquiv.trans (AlphaEquiv.trans h₁ h₂) h₃



/-- Because the AlphaEquiv relation is transitive, we can use the calc tactic. -/
example : AlphaEquiv
  ((ν "y") (("y"("z")∘ "z"⟨"x"⟩∘𝐨ₘ)))
  ((ν "u") (("u"("y")∘ "y"⟨"x"⟩∘𝐨ₘ)))
:= calc
  ((ν "y") (("y"("z")∘ "z"⟨"x"⟩∘𝐨ₘ))) =α ((ν "u") (("u"("z")∘ "z"⟨"x"⟩∘𝐨ₘ))) :=
    AlphaEquiv.cbn <| ChangeBoundName.res <| Finset.erase_eq_self.mp rfl
  _ =α ((ν "u") (("u"("y")∘ "y"⟨"x"⟩∘𝐨ₘ))) :=
  AlphaEquiv.cbn <| ChangeBoundName.res_traverse <| ChangeBoundName.inp "y" "u" "z" <|
    Finset.erase_eq_self.mp rfl



end AlphaEquiv



section Semantics

open Act

example :
  Tr (motive (pre (recv "x" "z") (motive (pre (send "z" "y") (motive nil))))) (name "x" "a")
    (motive (pre (send "a" "y") (motive nil)))
:= Tr.inp

example : Tr (motive (pre (send "a" "y") (motive nil))) (coname "a" "y") (motive nil) := Tr.out


example :
  Tr (motive (pre (recv "x" "z") (motive (pre (Prefix.guard "z" "y" (send "z" "w")) (motive nil)))))
      (name "x" "y") (motive (pre (Prefix.guard "y" "y" (send "y" "w")) (motive nil)))
:= Tr.inp

example :
  Tr (motive (pre (Prefix.guard "y" "y" (send "y" "w")) (motive nil))) (coname "y" "w") (motive nil)
:= Tr.mat Tr.out


example :
  Tr
    ((("x"("z")∘ "z"⟨"y"⟩∘ 𝐨ₘ) + "w"⟨"v"⟩∘ 𝐨ₘ)ₘ)
    (name "x" "a")
    (("a"⟨"y"⟩∘ 𝐨ₘ)ₘ)
:= Tr.sumL Tr.inp




example :
  ¬ ∃ s', Tr ((ν "z") ("z"⟨"w"⟩∘𝐨ₘ)) α s'
:= by
  intro hf
  cases hf
  case intro s' htr =>
    cases htr
    case res hn htr  =>
      cases htr
      contradiction
    case opn x htr =>
      have h := Tr.no_tr_from_diff_msg "z" x "w" "z" (p :=𝐨ₘ)
      specialize h (ne_of_beq_false rfl)
      apply h
      exists s'






/-Observability predicates on P₄ -/
example : P₄↓"y" :=
by
  apply Act.Obs_inp.inp (z := "_")
  exists (ν "z") ((["x" = "x"]("x"⟨"z"⟩))∘𝐨ₘ) ‖ ((ν "w") (("w"⟨"a"⟩∘𝐨ₘ)) ‖ (𝐨ₘ))
  refine Tr.res ?_ (Finset.erase_eq_self.mp rfl)
  · apply Tr.parR
    · refine Tr.res ?_ (Finset.erase_eq_self.mp rfl)
      · apply Tr.parR
        · exact Tr.sumR Tr.inp
        · exact Finset.empty_inter (({"w", "a"} ∪ ∅) \ ∅)
    · exact Finset.disjoint_iff_inter_eq_empty.mp fun ⦃x⦄ a a_1 => a

example : P₄↓-"x" :=
by
  apply Act.Obs_outp.outopn (z := "z")
  exists  𝐨ₘ ‖ ((ν "w") (("w"⟨"a"⟩∘𝐨ₘ)) ‖ (("w"("v")∘𝐨ₘ)+("y"("u")∘𝐨ₘ)))
  apply Tr.opn
  refine Tr.parL ?_ (Finset.disjoint_iff_inter_eq_empty.mp fun ⦃x⦄ a a_1 => a )
  · apply Tr.mat
    apply Tr.out

example : ¬ (∃ x, x ≠ "y" ∧ P₄↓ x) :=
by
  intro hexists
  cases hexists
  case intro x h =>
    cases h.2
    case inp z he
    have ⟨P', htr⟩ := he
    cases htr
    case res P' hn htr =>
      cases htr
      case parL P' htr hbnd =>
        cases htr
        case mat htr =>
          cases htr
      case parR Q' hbnd htr =>
        cases htr
        case res P' hn htr =>
          cases htr
          case parL _ htr _ =>
            cases htr
          case parR _ _ htr =>
            cases htr
            case sumL P' htr =>
              cases htr
              apply hn
              simp only [Act.n]
              exact Finset.mem_insert_self "w" {z}
            case sumR Q' htr =>
              cases htr
              exact h.1 rfl


example : ¬ (∃ y, y ≠ "x" ∧ P₄↓- y) :=
by
  intro hf
  have ⟨y,hneq,hobs⟩ := hf
  cases hobs
  case outp z htr =>
    have ⟨P',htr⟩ := htr
    cases htr
    case res _ _ htr =>
      cases htr
      case parL _ htr _ =>
        cases htr
        case mat htr =>
          cases htr
          contradiction
      case parR _ _ htr =>
        cases htr
        case res _ _ htr =>
          cases htr
          case parL _ htr _ =>
            cases htr
            case out _ _ hn _ =>
            exfalso
            apply hn
            exact Finset.insert_eq_self.mp rfl
          case parR htr =>
            cases htr
            case sumL htr | sumR htr => cases htr
  case outopn z htr =>
    have ⟨_,htr⟩ := htr
    cases htr
    case res htr =>
      cases htr
      case parL htr _  =>
        cases htr
        case mat htr =>
        cases htr
      case parR htr =>
        cases htr
        case res htr =>
          cases htr
          case parL htr _ => cases htr
          case parR htr =>
            cases htr
            case sumL htr | sumR htr => cases htr
        case opn htr =>
          cases htr
          case parL P' htr _ =>
            apply Tr.no_tr_from_diff_msg "w" y  "a" "w" (p := 𝐨ₘ) (ne_of_beq_false rfl)
            exists P'
          case parR htr =>
            cases htr
            case sumL htr | sumR htr => cases htr
    case opn p' htr =>
      cases htr
      case parL htr _  =>
        cases htr
        case mat htr =>
        cases htr
        contradiction
      case parR htr =>
        cases htr
        case res htr =>
          cases htr
          case parL p' htr _ =>
            apply Tr.no_tr_from_diff_msg "w" y  "a" "z" (ne_of_beq_false rfl)
            exists p'
          case parR  _ htr => exact (match htr with | .sumL htr | .sumR htr => by cases htr)



end Semantics


section BehaviouralTheory


/-- Example of two bisimilar process (from [Sangiorgi2011]) -/
inductive R : Process Name → Process Name → Prop where
| a (hdiffs : z ≠ a ∧ z ≠ w ∧ z ≠ x ∧ a ≠ w ∧ a ≠ x ∧ w ≠ x) :
  R ((ν z) ((z⟨a⟩∘𝐨ₘ)‖ z(w)∘x⟨w⟩∘𝐨ₘ)) (Process.motive (Motive.pre Prefix.τ (x⟨a⟩∘ 𝐨ₘ)))
| b (hdiffs : z ≠ a ∧ z ≠ x ∧ a ≠ x)
  : R ((ν z) (𝐨ₘ‖ (x⟨a⟩∘𝐨ₘ)ₘ)) ((x⟨a⟩∘𝐨ₘ)ₘ)
| c
  : R ((ν z) (𝐨ₘ ‖ 𝐨ₘ)) (𝐨ₘ)

example [HasFresh Name] [DecidableEq Name]
  (hdiffs : z ≠ a ∧ z ≠ w ∧ z ≠ x ∧ a ≠ w ∧ a ≠ x ∧ w ≠ x)
  : ((ν z) ((z⟨a⟩∘𝐨ₘ)‖ (z(w)∘x⟨w⟩∘𝐨ₘ))) ~[lts (Name := Name)]
  (Process.motive (Motive.pre Prefix.τ (x⟨a⟩∘ 𝐨ₘ)))
:=
by
  exists R
  constructor
  · exact R.a hdiffs
  · intros s₁ s₂ hr μ
    constructor
    · intros s₁' htr
      cases hr
      case a z a w x h hdiff =>
        cases htr
        case res p' hnotin htr =>
          exists ((h⟨w⟩∘𝐨ₘ)ₘ)
          cases htr
          case parL _ htr _ =>
            cases htr
            simp only [Act.n] at hnotin
            exfalso
            apply hnotin
            exact Finset.mem_insert_self a {w}
          case parR _ _ htr =>
            cases htr
            simp only [Act.n] at hnotin
            exfalso
            apply hnotin
            apply Finset.mem_insert_self a
          case comm μ p' μ' q' hco htr₁ htr₂ =>
            apply And.intro Tr.tau
            cases htr₁
            cases hco
            cases htr₂
            simp only [HasSubstitution.subst,Process.subst,Motive.subst,Prefix.subst]
            have h': h ≠ x := (fun hf => hdiff.2.2.2.2.2 (Eq.symm hf))
            simp only [ite_self]
            simp only [h',reduceIte]
            apply R.b <| And.intro hdiff.1 (And.intro hdiff.2.2.1 hdiff.2.2.2.2.1)
          case closeL x' z' p' q'  htr₁ htr₂ hn₁ =>
            cases htr₁
        case opn x' htr =>
          cases htr
          case parL _ htr _ =>
            cases htr
            exfalso
            apply hdiff.1 rfl
          case parR htr =>
            cases htr
      case b z a w x hdiff =>
        exists 𝐨ₘ
        cases htr
        case res p' hn htr =>
          cases htr
          case parL p' htr hinter =>
            contradiction
          case parR q' hinter htr =>
            cases htr
            apply And.intro
            · apply Tr.out
            · exact R.c
          repeat contradiction
        case opn x htr =>
          cases htr
          · contradiction
          case parR q' hinter htr =>
            cases htr
            exfalso
            apply hdiff.1
            rfl
      case c z =>
        cases htr
        case res _ _ htr =>
          cases htr
          repeat contradiction
        case opn _ _ htr =>
          cases htr
          repeat contradiction
    · intro s₂' htr
      cases hr
      case a z a w x hdiff =>
        cases htr
        case tau =>
          exists ((ν z) (𝐨ₘ‖ (x⟨a⟩∘𝐨ₘ)ₘ))
          constructor
          · apply Tr.res
            · apply Tr.comm (μ := Act.coname z a) (μ' := Act.name z a)
              · apply Tr.out (p := 𝐨ₘ)
              · apply Tr.inp_subst
                simp only [HasSubstitution.subst,Process.subst,Motive.subst,Prefix.subst]
                have h : x ≠ w := fun hf => hdiff.2.2.2.2.2 (Eq.symm hf)
                simp only [h,reduceIte,Prefix.bn]
                rfl
              · exact Act.Co.cn
            · simp only [Act.n]
              exact Finset.notMem_empty z
          · exact R.b ⟨hdiff.1,hdiff.2.2.1,hdiff.2.2.2.2.1⟩
      case b z a x hdiff =>
        cases htr
        case out =>
          exists ((ν z) (𝐨ₘ ‖ 𝐨ₘ))
          constructor
          · apply Tr.res
            · apply Tr.parR Tr.out
              simp only [Act.bn,Process.fn,Motive.fn]
              exact Finset.empty_inter ∅
            · simp only [Act.n]
              intro hf
              simp only [Finset.mem_insert, Finset.mem_singleton] at hf
              exact (
                match hf with
                | .inl hf => hdiff.2.1 hf
                | .inr hf => hdiff.1 hf
              )
          · exact R.c
      case c z =>
        cases htr


end BehaviouralTheory

end CslibTests
