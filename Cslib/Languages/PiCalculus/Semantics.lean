/-
Copyright (c) 2026 Danaël Carbonneau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Danaël Carbonneau, Fabrizio Montesi
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Languages.PiCalculus.Basic

@[expose] public section

/-! # Semantics of PiCal

## Main definitions
- `PiCal.Tr`: transition relation for PiCal.
- `PiCal.lts`: the `LTS` of PiCal.

## References

* [D. Sangiorgi, *Introduction to Bisimulation and Coinduction*][Sangiorgi2011]
* [D. Sangiorgi and D. Walker, *The Pi-Calculus: A Theory of Mobile Processes*][Sangiorgi2001].

-/

namespace Cslib

namespace PiCal

open Process
open Motive
open Prefix
open Act

/-- The transition relation for PiCal. -/
@[lts PiCal.lts]
inductive Tr [DecidableEq Name] [HasFresh Name] : Process Name →
 Act Name → Process Name → Prop
where
  | out : Tr (motive (pre (send x y) p)) (coname x y) p
  | inp : Tr (motive (pre (recv x y) p)) (name x z) (p[y:=z])
  | tau : Tr (motive (pre τ p)) τ p
  | mat : Tr (motive (pre π p)) α p' → Tr (motive (pre (Prefix.guard x x π) p)) α p'
  | sumL : Tr (motive p) α (motive p') →  Tr (motive (sum p q)) α (motive p')
  | sumR : Tr (motive q) α (motive q') →  Tr (motive (sum p q)) α (motive q')
  | parL : Tr p α p' → α.bn ∩ q.fn = ∅ → Tr (par p q) α (par p' q)
  | parR : Tr q α q' → α.bn ∩ p.fn = ∅ → Tr (par p q) α (par p q')
  | comm : Tr p μ p' → Tr q μ' q' → (Act.Co μ μ') → Tr (par p q) τ (par p' q')
  | closeL : Tr p (conameB x z) p' → Tr q (name x z) q' → z ∉ q.fn →
    Tr (par p q) τ (res z (par p' q'))
  | res : Tr p α p' → z ∉ α.n → Tr (res z p) α (res z p')
  | opn : Tr p (coname x z) p' → Tr (res z p) (conameB x z) p'
  | repl : Tr (bang a x p) (name a v) (par (bang a x p) (p[x:=v]))


/-- Helper for proofs when a transition is not possible because the channels are different.
  If a ≠ b, there is not transition from a process prefixed by a with (coname b y) as label.
-/
theorem Tr.no_tr_from_diff_chn [HasFresh Name] [DecidableEq Name] (a b x y : Name):
  a ≠ b →
  ¬ ∃ s',
  Tr ((a⟨x⟩∘p)ₘ) (coname b y) s'
:= by
  intro hneq hf
  cases hf
  case intro s' htr =>
    cases htr
    case out =>
      contradiction
/-- Helper for proofs when a transition is not possible because the sent messages are different.
  If x ≠ y, there is not transition from a process prefixed by a⟨x⟩ with (coname b y) as label.
-/
theorem Tr.no_tr_from_diff_msg [HasFresh Name] [DecidableEq Name] (a b x y : Name) :
  x ≠ y →
  ¬ ∃ s',
  Tr ((a⟨x⟩∘p)ₘ) (coname b y) s'
:= by
  intro hneq hf
  cases hf
  case intro s' htr =>
    cases htr
    contradiction
/--
Helper for proofs about transitions that use substitution. Applied to a goal of the
form `Tr x(y)∘p (name x z) p', there remains a proof that p[y:=z] is equal to p'.
If p' = p[y:=z], there is a transition from x(y)ᵒp to p' with label (name x z)
-/
theorem Tr.inp_subst [DecidableEq Name] [HasFresh Name] {p p' : Process Name}
  (hsubst : p' = p[y:=z])
  : Tr (motive (pre (recv x y) p)) (name x z) p'
:=
by
  rw[hsubst]
  exact Tr.inp

/-- No transition with z as a name of the label that is not bound can occur from a
process of the form (ν z) p. -/
theorem Tr.no_tr_from_res [DecidableEq Name] [HasFresh Name] {p : Process Name}
  : z ∈ μ.n ∧ z ∉ μ.bn → ¬ (∃p', Tr ((Process.res z p)) μ p' )
:= by
  intros hin hf
  have ⟨p',htr⟩ := hf
  cases htr
  case res p' hn htr  => exact hn hin.1
  case opn y htr =>
    simp only [Act.bn] at hin
    apply hin.2 <| Finset.mem_singleton.mpr rfl



section observability

/- Observability of a transition (inputs) -/
inductive Act.Obs_inp [HasFresh Name] [DecidableEq Name] : Process Name → Name → Prop where
| inp (x : Name) (P : Process Name ):  ( ∃ P', Tr P (Act.name x z) P') → Obs_inp P x
/- Observability of a transition (outputs)-/
inductive Act.Obs_outp [HasFresh Name] [DecidableEq Name] : Process Name → Name → Prop where
| outp {z} (x : Name) (P : Process Name) : (∃ P', Tr P (Act.coname x z) P') → Obs_outp P x
| outopn {z} (x : Name) (P : Process Name) : (∃ P', Tr P (Act.conameB x z) P') → Obs_outp P x

/-- Notation for the observaibility predicates-/
notation:65 P"↓"μ => Act.Obs_inp P μ
notation:65 P"↓-"μ => Act.Obs_outp P μ







end observability


end PiCal
end Cslib
