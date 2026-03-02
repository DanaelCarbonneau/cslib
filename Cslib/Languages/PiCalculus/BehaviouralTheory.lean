
module

public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Cslib.Languages.PiCalculus.Semantics

@[expose] public section

/-! # Behavioural theory of CCS

## Main results

- `CCS.bisimilarityCongruence`: bisimilarity is a congruence in CCS.

Additionally, some standard laws of bisimilarity for CCS, including:
- `CCS.bisimilarity_par_nil`: P | 𝟎 ~ P.
- `CCS.bisimilarity_par_comm`: P | Q ~ Q | P
- `CCS.bisimilarity_choice_comm`: P + Q ~ Q + P
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


-- /-- P | 𝟎 ~ P -/
-- @[simp, scoped grind .]
-- theorem bisimilarity_par_nil : (par p nil) ~[lts (defs := defs)] p := by
--   unfold lts at *
--   exists ParNil, .parNil
--   intro _ _ _ _
--   constructor
--   case left => grind
--   case right =>
--     intro s2' htr
--     exists par s2' nil
--     grind

-- theorem bisimilarity_par_nil : (p ‖ ∘) ~[lts (Name := Name) (Constant := Constant)] p :=
-- by
--   unfold lts at *
--   exists ParNil -- relation entre les deux processus
--   exists .parNil -- preuve que les deux processus sont dans la relation
--   intro s1 s2 hrs1s2 μ -- On prend deux processus qui sont dans la relation, et une étiquette μ
--   constructor -- deux côtés à montrer pour la bisimulation
--   case left =>
--     intro s1' htr
--     cases hrs1s2
--     case parNil pn =>
--       cases htr <;> try contradiction -- il n'y a qu'une tr possible, et c'est parL
--       case parL p' htr' =>
--         exists p'
--         exact ⟨htr', .parNil⟩
--   case right =>
--     intro s2' htr
--     exists par s2' nil
--     constructor
--     · cases hrs1s2
--       exact Tr.parL htr
--     · exact .parNil


/-- P | 𝟎 ~ P -/
@[simp, scoped grind .]
theorem bisimilarity_par_nil [HasFresh Name] :
  (p ‖ ∘) ~[lts (Name := Name) (Constant := Constant)] p :=
  by
    unfold lts at *
    exists ParNil -- relation entre les deux processus
    exists .parNil -- preuve que les deux processus sont dans la relation
    intro s1 s2 hrs1s2 μ -- On prend deux processus qui sont dans la relation, et une étiquette μ
    constructor -- deux côtés à montrer pour la bisimulation
    · grind -- grind permet d'automatiser les preuves ! (ça peut prendre du temps par contre)
    · intro s2' htr
      exists par s2' nil
      grind


@[local grind]
private inductive ParComm : Process Name Constant → Process Name Constant → Prop where
| parComm : ParComm (par p q) (par q p)
--| parCommRes :  ParComm ((ν a) (par p q)) ((ν a) (par q p))

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
      case com μ p'' μ'  q'' hco htr₁ htr₂ =>
        exists (q'' ‖ p'')
        grind
      case clsL a b p'' q'' htr₁ htr₂ =>

        sorry
      --   exists (ν b) (q''‖ p'')
      --   grind
      -- case clsR a b p'' q'' htr₁ htr₂ =>
      --   exists (ν b) (q''‖ p'')
      --   grind
      repeat sorry
  · sorry




  -- sorry



end PiCal

end PiCal.BehaviouralTheory

end Cslib
