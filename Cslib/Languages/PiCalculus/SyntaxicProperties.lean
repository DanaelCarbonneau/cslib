
/-
Copyright (c) 2026 Danaël Carbonneau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Danaël Carbonneau
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Languages.PiCalculus.Basic
public import Cslib.Languages.PiCalculus.Semantics

@[expose] public section

/-! # Syntaxic Properties of the pi calculus

## Main definitions

## References

* [D. Sangiorgi and D. Walker, *The Pi-Calculus: A Theory of Mobile Processes*][Sangiorgi2001].

-/

namespace Cslib

namespace PiCal

open Process
open Motive
open Prefix
open Act




mutual
theorem Process.subst_subset [DecidableEq Name] [HasFresh Name] (P : Process Name) (x v : Name) :
  P[x:=v].fn ⊆ P.fn ∪ {v}
:= by
  cases P
  case motive m =>
    have hmut := m.subst_subset x v
    simp only [HasSubstitution.subst,Process.subst] at *
    simp only [Process.fn]
    assumption
  case par p₁ p₂ =>
    have hind₁ := p₁.subst_subset x v
    have hind₂ := p₂.subst_subset x v
    simp only [HasSubstitution.subst,Process.subst, Process.fn] at *
    grind
  case res z p =>
    have hind := p.subst_subset x v
    simp only [HasSubstitution.subst,Process.subst] at *
    split
    case isTrue =>
      simp only [Process.fn]
      exact Finset.subset_union_left
    case isFalse =>
      split
      case isTrue ht =>
        simp only [Process.fn]
        have hfresh := HasFresh.fresh_notMem ((νz)p).n
        let fr := fresh ((νz)p).n
        have heq : fr = fresh ((νz)p).n := rfl
        rw[←heq] at *
        rw[ht]
        rw[Finset.sdiff_union_self_eq_union]
        have hind' := p.subst_subset z fr
        simp only [HasSubstitution.subst] at hind'
        grind
      case isFalse hf =>
        simp only [Process.fn]
        grind
  case bang a x' p =>
    have hind := p.subst_subset x v
    simp only [HasSubstitution.subst,Process.subst] at *
    split
    case isTrue ht =>
      split
      case isTrue ht' =>

        sorry
      sorry
    sorry
theorem Motive.subst_subset [DecidableEq Name] [HasFresh Name] (M : Motive Name) (x v : Name) :
  M[x:=v].fn ⊆ M.fn ∪ {v}
:= by
  cases M
  case nil =>
    simp only [HasSubstitution.subst,Motive.subst,Motive.fn]
    exact Finset.empty_subset (∅ ∪ {v})
  case pre π p =>
    have hmut := p.subst_subset x v
    simp only[HasSubstitution.subst,Motive.subst, Motive.fn] at *
    induction π
    case send a b =>
      simp only [Prefix.subst,Prefix.fn,Prefix.bn]
      split
      · split
        · split
          ·grind
          ·grind
        · grind
      · split
        · split
          ·grind
          ·grind
        · grind
    case recv a b =>
      simp only [Prefix.subst,Prefix.fn,Prefix.bn]
      split
      · split
        · grind
        · grind
      · split
        · grind
        · grind
    case τ =>
      simp only [Prefix.subst,Prefix.fn,Prefix.bn]
      grind
    case guard x' y' π hind =>
      simp only [Prefix.subst,Prefix.fn,Prefix.bn]

      split
      · split
        · split
          · expose_names
            simp only[h_2,↓reduceIte] at hind
            rw[h_1,h]
            have h : (π.fn ∪ p.fn) \ π.bn ∪ {v} ⊆  ({x, x} ∪ π.fn ∪ p.fn) \ π.bn ∪ {v} := by
              grind
            grind
          · expose_names
            simp only[h_2,↓reduceIte] at hind
            rw[h_1,h]

            repeat sorry
        repeat sorry
      repeat sorry

  case sum => sorry

end

theorem tr_fn[DecidableEq Name] [HasFresh Name] (P P' : Process Name):
  Tr P α P' →
    (
      match α with
      | Act.coname x y => x ∈ P.fn ∧ y ∈ P.fn ∧ P'.fn ⊆ P.fn
      | Act.name x y => x ∈ P.fn ∧ P'.fn ⊆ P.fn ∪ {y}
      | Act.conameB x z => x ∈ P.fn ∧ P'.fn ⊆ P.fn ∪ {z}
      | Act.τ => P'.fn ⊆ P.fn
    )
:= by
  intro Htr
  cases α
  case name a b =>
    simp only [Finset.union_singleton]
    cases Htr
    case inp y p =>
      constructor
      · simp only [Process.fn,Motive.fn,Prefix.fn,Prefix.bn]
        refine Finset.mem_sdiff.mpr ?_
        constructor
        · grind
        · -- faux dans le cas général (a peut être égal à y ! Mais le veut-on ?)
          sorry
      · have h := Process.subst_subset p y b
        simp only [HasSubstitution.subst,Process.fn,Motive.fn,Prefix.fn, Prefix.bn] at *
        have h' : p.fn ∪ {b} ⊆ insert b (({a} ∪ p.fn)) \ {y}:=
          by

            sorry

        sorry
    repeat sorry
  case coname a b => sorry
  case conameB a b => sorry
  case τ =>
    simp only
    cases Htr
    repeat sorry


end PiCal
end Cslib
