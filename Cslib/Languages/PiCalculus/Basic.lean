/-
Copyright (c) 2026 Danaël Carbonneau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Danaël Carbonneau
-/

module

public import Cslib.Foundations.Syntax.Context
public import Cslib.Foundations.Syntax.Congruence
public import Cslib.Foundations.Data.HasFresh
public import Cslib.Foundations.Syntax.HasAlphaEquiv
public import Cslib.Foundations.Syntax.HasSubstitution

@[expose] public section

/-! # Pi calculus


## Main definitions
- `PiCal.Process`: processes.

## Main results


## References

* [D. Sangiorgi, *Introduction to Bisimulation and Coinduction*][Sangiorgi2011]
* [D. Sangiorgi and D. Walker, *The Pi-Calculus: A Theory of Mobile Processes*][Sangiorgi2001].

-/

namespace Cslib.PiCal

universe u v


/-- Actions. -/
inductive Act (Name : Type u) : Type u where
  | name (a : Name) (b : Name)
  | coname (a : Name) (b : Name)
  | conameB (a : Name) (b : Name)
  | τ
deriving DecidableEq


/-- Free names within an action. -/
def Act.fn [DecidableEq Name] (α : Act Name) : Finset Name :=
  match α with
  | name a b => {a,b}
  | coname a b => {a,b}
  | conameB a _ => {a}
  | τ => ∅

/-- Bound names within an action. -/
def Act.bn [DecidableEq Name] (α : Act Name) : Finset Name :=
  match α with
  | conameB _ b => {b}
  | _ => ∅

/-- Names within an action. -/
def Act.n [DecidableEq Name] (α : Act Name) : Finset Name :=
  match α with
  | name a b | coname a b | conameB a b => {a,b}
  | τ => ∅

/-- The names of an action is the union of its bound and free names. -/
theorem Act.n_union_fn_bn [DecidableEq Name] (μ : Act Name) : μ.n = μ.fn ∪ μ.bn :=
  match μ with
  | name a b | coname a b => Eq.symm (Finset.union_empty {a,b})
  | conameB a b => Finset.insert_eq a {b}
  | τ => rfl


/-- Prefixes. -/
inductive Prefix (Name : Type u) : Type u where
  | send (a b : Name)
  | recv (a b : Name)
  | τ
  | guard (x y : Name) (π : Prefix Name)

/-- Free names within a prefix. -/
def Prefix.fn [DecidableEq Name] : (π : Prefix Name) → Finset Name
  | send a b => {a,b}
  | recv a _ => {a}
  | τ => ∅
  | guard x y π => {x,y} ∪ π.fn

/-- Bound names within a prefix. -/
def Prefix.bn [DecidableEq Name] : (π : Prefix Name) → Finset Name
  | send _ _ | τ => ∅
  | recv _ b => {b}
  | guard _ _ π => π.bn

/-- Names within a prefix. -/
def Prefix.n [DecidableEq Name] : (π : Prefix Name) → Finset Name
  | send a b => {a,b}
  | recv a b => {a,b}
  | τ => ∅
  | guard x y π => {x,y} ∪ π.n

/-- The names of a prefix are the union of its bound and free names -/
theorem Prefix.n_union_fn_bn [DecidableEq Name] (π : Prefix Name) :
  π.n = π.bn ∪ π.fn
:= by
  induction π
  case send | τ => rfl
  case recv a b =>
    simp only [Prefix.bn,Prefix.fn,Prefix.n]
    exact Eq.symm (Finset.union_singleton a {b})
  case guard x y π hind =>
    simp only [Prefix.bn,Prefix.fn,Prefix.n]
    rw[hind]
    exact Finset.union_left_comm {x, y} π.bn π.fn

/-- Substitution within a prefix -/
def Prefix.subst [DecidableEq Name] (μ : Prefix Name) (x v : Name) : Prefix Name :=
  match μ with
  | send a x' =>
    send (if a = x then v else a) (if x' = x then v else x')
  | recv a x' => recv (if a = x then v else a) x'
  | τ => τ
  | guard a b π => guard (if a = x then v else a) (if b = x then v else b) (π.subst x v)




mutual

/--
  Mutual definition of both motives and process

  P ::= M | P ‖ P | (ν z) P | !a(x).P
  M ::= 𝐨 | π.P | M + M

  The mutual definition comes from [Sangiorgi2001], it mostly restricts the way the sum operator can
  be used : there can only be sums of prefixed or nil processi.
  We added a restriction regarding replication, which only allows it under the reception
  of an input.
-/
inductive Motive (Name : Type u) : Type u where
  | nil
  | pre (π : Prefix Name) (P : Process Name)
  | sum (m₁ m₂ : Motive Name)
inductive Process (Name : Type u) : Type u where
  | motive (m : Motive Name)
  | par (p₁ p₂ : Process Name)
  | res (z : Name) (p: Process Name)
  | bang (a x : Name) (p : Process Name)
end






open Motive Process Prefix


mutual
/-- Motive and Process free names. -/
def Motive.fn [DecidableEq Name] : (π : Motive Name) → Finset Name
  | nil => ∅
  | pre π P => (π.fn ∪ P.fn) \ π.bn
  | sum m₁ m₂ => m₁.fn ∪ m₂.fn
def Process.fn [DecidableEq Name] : (π :  Process Name) → Finset Name
  | motive m => m.fn
  | par p₁ p₂ => p₁.fn ∪ p₂.fn
  | res z p => p.fn \ {z}
  | bang a x p => (p.fn ∪ {a})\ {x}
end


mutual
/-- Motive and Process bound names. -/
def Motive.bn [DecidableEq Name] : (π : Motive Name) → Finset Name
  | nil => ∅
  | pre π P => (π.bn ∪ P.bn)
  | sum m₁ m₂ => m₁.bn ∪ m₂.bn
def Process.bn [DecidableEq Name] : (π :  Process Name) → Finset Name
  | motive m => m.bn
  | par p₁ p₂ => p₁.bn ∪ p₂.bn
  | res z p => p.bn ∪ {z}
  | bang _ x p => (p.bn ∪ {x})
end
mutual
/-- Motive and Process names. -/
def Motive.n [DecidableEq Name] : (π : Motive Name) → Finset Name
  | nil => ∅
  | pre π P => π.n ∪ P.n
  | sum m₁ m₂ => m₁.n ∪ m₂.n
def Process.n [DecidableEq Name] : (π :  Process Name) → Finset Name
  | motive m => m.n
  | par p₁ p₂ => p₁.n ∪ p₂.n
  | res z p => p.n ∪ {z}
  | bang a x p => p.n ∪ {a} ∪ {x}
end

mutual
/-- The names of a Process/Motive are the union of its bound and free names -/
theorem Process.n_union_fn_bn [DecidableEq Name] (p : Process Name) :
  p.n = p.fn ∪ p.bn
:= by
  cases p
  case motive m =>
    have h_mutual := Motive.n_union_fn_bn m
    simp only [Process.n,Process.fn,Process.bn]
    exact h_mutual
  case par p₁ p₂ =>
    have hind₁ := Process.n_union_fn_bn p₁
    have hind₂ := Process.n_union_fn_bn p₂
    simp only [Process.n,Process.fn,Process.bn]
    have h :  p₁.fn ∪ p₂.fn ∪ (p₁.bn ∪ p₂.bn) =  (p₁.fn ∪ p₁.bn) ∪ (p₂.fn ∪ p₂.bn) :=
      by
        exact Finset.union_union_union_comm p₁.fn p₂.fn p₁.bn p₂.bn
    rw[h]
    rw[←hind₁,←hind₂]
  case res z p =>
    have hind := Process.n_union_fn_bn p
    simp only [Process.n,Process.fn,Process.bn]
    rw[hind]
    have h : p.fn \ {z} ∪ (p.bn ∪ {z}) = (p.fn \ {z}) ∪ {z} ∪ p.bn :=
      by
        rw[Finset.union_comm p.bn {z}]
        exact Eq.symm (Finset.union_assoc (p.fn \ {z}) {z} p.bn)
    have h' : p.fn \ {z} ∪ {z} = p.fn ∪ {z} := Finset.sdiff_union_self_eq_union
    rw[h]
    rw[Finset.sdiff_union_self_eq_union]
    exact Finset.union_right_comm p.fn p.bn {z}
  case bang a x p =>
    have hind := Process.n_union_fn_bn p
    simp only [Process.n,Process.fn,Process.bn]
    rw[Finset.union_comm p.bn {x}]
    rw[←Finset.union_assoc ((p.fn ∪ {a}) \ {x})]
    rw[Finset.sdiff_union_self_eq_union]
    rw[hind]
    grind

theorem Motive.n_union_fn_bn [DecidableEq Name] (m : Motive Name) :
  m.n = m.fn ∪ m.bn
:= by
  cases m
  case nil => rfl
  case pre π p =>
    have hmut := p.n_union_fn_bn
    have hpre := π.n_union_fn_bn
    simp only [Motive.n,Motive.fn,Motive.bn]
    rw[←Finset.union_assoc ((π.fn ∪ p.fn) \ π.bn)]
    rw[Finset.sdiff_union_self_eq_union]
    rw[hpre,hmut]
    grind
  case sum m₁ m₂ =>
    have hind₁ := m₁.n_union_fn_bn
    have hind₂ := m₂.n_union_fn_bn
    simp only [Motive.n,Motive.fn,Motive.bn]
    grind
end


mutual
/-- Substitution for Motives and Process -/
def Motive.subst [HasFresh Name] [DecidableEq Name] (m : Motive Name) (x v : Name) :=
  match m with
  | nil => nil
  | pre π p => pre (π.subst x v) (if x ∈ π.bn then p else p.subst x v)
  | sum m₁ m₂ =>  sum (m₁.subst x v) (m₂.subst x v)
def Process.subst  [HasFresh Name] [DecidableEq Name] (p : Process Name) (x v : Name)
  : Process Name :=
  match p with
  | par p₁ p₂ => par  (p₁.subst x v) (p₂.subst x v)
  | motive m => motive (m.subst x v)
  | bang a x' p =>
    bang
    (if a = x then v else a)
    (if x = x' then v else x')
    (if x = x' then p else p.subst x v)
  | res a p' =>
      if a = x then res a p' --
      else
      if a = v then
        let a' := HasFresh.fresh p.n
        res a' (p'.subst a a')
      else res a (p'.subst x v)
end

instance instSubstitutionProcess [DecidableEq Name] [HasFresh Name] :
    HasSubstitution (Process Name) Name Name where
  subst := Process.subst

instance instSubstitutionMotive [DecidableEq Name] [HasFresh Name] :
    HasSubstitution (Motive Name) Name Name where
  subst := Motive.subst

instance instSubstitutionPrefix [DecidableEq Name] :
    HasSubstitution (Prefix Name) Name Name where
  subst := Prefix.subst



/-- Substituting a name by itself in a prefix does not change it -/
theorem Prefix.subst_idem [DecidableEq Name] (π : Prefix Name) (x : Name) :
    π.subst x x = π
  := by
  induction π
  case send a b =>
    simp only [Prefix.subst]
    simp only [send.injEq, ite_eq_right_iff]
    apply And.intro (fun h => Eq.symm h) (fun h => Eq.symm h)
  case recv a b =>
    simp only [Prefix.subst]
    simp only [recv.injEq,ite_eq_right_iff]
    exact And.intro (fun h => Eq.symm h) trivial
  case τ => rfl
  case guard x' y π hind =>
    simp only [Prefix.subst]
    simp only [guard.injEq,ite_eq_right_iff]
    constructor
    · exact (fun h => Eq.symm h)
    constructor
    · exact (fun h => Eq.symm h)
    · exact hind


mutual
/-- Substituting a name by itself in a Motive/Process does not change it -/
theorem Motive.subst_idem [DecidableEq Name] [HasFresh Name] (m : Motive Name) (x : Name) :
  m.subst x x = m
:= by
  cases m
  case nil =>
    simp only [Motive.subst]
  case pre π P =>
    simp only [Motive.subst]
    have hmut := P.subst_idem x
    rw[hmut]
    rw[Prefix.subst_idem]
    rw[ite_self]
  case sum m₁ m₂ =>
    have hind₁ := m₁.subst_idem x
    have hind₂ := m₂.subst_idem x
    simp only [Motive.subst]
    rw[hind₁,hind₂]

theorem Process.subst_idem [DecidableEq Name] [HasFresh Name] (p : Process Name) (x : Name) :
  p.subst x x = p
:= by

  cases p
  case motive m =>
    simp only [Process.subst]
    rw[m.subst_idem]
  case par p₁ p₂ =>
    simp only [Process.subst]
    rw[p₁.subst_idem,p₂.subst_idem]
  case res z p =>
    simp only [Process.subst]
    split
    · rfl
    · rw[p.subst_idem]
  case bang a x' p =>
    simp only [Process.subst]
    simp only [bang.injEq,ite_eq_right_iff]
    rw[p.subst_idem]
    exact ⟨(fun h => Eq.symm h), id,  (ite_id p)⟩

end




open Act

/-- An action is visible if it is a name or a coname. -/
@[scoped grind]
inductive Act.IsVisible : Act Name → Prop where
  | name : IsVisible (Act.name a b)
  | coname : IsVisible (Act.coname a b)
  | coname_open : IsVisible (Act.conameB a b)


/-- If an action is visible, it is not `τ`. -/
@[scoped grind →, simp]
theorem isVisible_neq_τ {μ : Act Name} (h : μ.IsVisible) : μ ≠ Act.τ := by
  cases μ <;> grind

/-- Checks that an action is the coaction of another. -/
@[scoped grind]
inductive Act.Co {Name : Type u} : Act Name → Act Name → Prop where
  | nc : Co (name a b) (coname a b)
  | cn : Co (coname a b) (name a b)
  | nco : Co (name a b) (conameB a b)
  | cno : Co (conameB a b) (name a b)

/-- `Act.Co` is symmetric. -/
@[scoped grind →, symm]
theorem Co.symm (h : Act.Co μ μ') : Act.Co μ' μ := by grind

/-- If two actions are one the coaction of the other, then they are both visible. -/
@[scoped grind →]
theorem co_isVisible (h : Act.Co μ μ') : μ.IsVisible ∧ μ'.IsVisible := by grind

/-- Checks that an action is the coaction of another. This is the Boolean version of `Act.Co`. -/
@[scoped grind =]
def isCo [DecidableEq Name] (μ μ' : Act Name) : Bool :=
  match μ, μ' with
  | name a x, coname b y | coname a x, name b y | conameB a x, name b y
    | name a x, conameB b y => a = b ∧ x = y
  | _, _ => false

theorem isCo_iff [DecidableEq Name] {μ μ' : Act Name} : isCo μ μ' ↔ Co μ μ' := by
  grind [cases Act]

/-- `Act.Co` is decidable if `Name` equality is decidable. -/
instance [DecidableEq Name] {μ μ' : Act Name} : Decidable (Co μ μ') :=
  decidable_of_decidable_of_iff isCo_iff




/-- Change of a Bound name in a process
  (replacement of a subterm x(z).Q by x(w).Q[z:=w], or of a subterm (ν z) Q by (ν w) Q[z:=w] where
  in each case w does not occur in Q [Sangiorgi2011])
  )
-/
inductive Process.ChangeBoundName [DecidableEq Name] [HasFresh Name]
  : Process Name → Process Name → Prop where
| inp (z x y : Name) : z ∉ p.fn → ChangeBoundName
  (Process.motive (Motive.pre (Prefix.recv x y) p))
  (Process.motive (Motive.pre (Prefix.recv x z) (p.subst y z)))
| res : z ∉ p.fn → ChangeBoundName (res x p) (res z (p.subst x z))
| bang :  z ∉ p.fn → ChangeBoundName
  (Process.bang x y p)
  (Process.bang x z (p.subst y z))
| bang_traverse : ChangeBoundName p q → ChangeBoundName (bang x y p) (bang x y q)
| res_traverse :  ChangeBoundName p q → ChangeBoundName (res x p) (res x q)
| par_traverseL : ChangeBoundName p p' → ChangeBoundName (par p q) (par p' q)
| par_traverseR : ChangeBoundName q q' → ChangeBoundName (par p q) (par p q')
| prefix_traverse : ChangeBoundName p q → ChangeBoundName (motive (pre π p)) (motive (pre π q))
| choice_traverseL : ChangeBoundName (motive p) (motive p') →
  ChangeBoundName (motive (sum p q)) (motive (sum p' q))
| choice_traverseR : ChangeBoundName (motive q) (motive q') →
  ChangeBoundName (motive (sum p q)) (motive (sum p q'))

/-- α-equivalence : P and Q are α-convertible if Q can be obtained from P by a finite number of
  change of bound names
-/
inductive Process.AlphaEquiv [DecidableEq Name] [HasFresh Name] : Process Name → Process Name →
Prop where
| cbn : ChangeBoundName p q → AlphaEquiv p q
/- Equivalence properties -/
| refl : AlphaEquiv p p
| symm : AlphaEquiv p q → AlphaEquiv q p
| trans : AlphaEquiv p1 p2 → AlphaEquiv p2 p3 → AlphaEquiv p1 p3

instance instHasAlphaEquivProcess [DecidableEq Name] [HasFresh Name]
  : HasAlphaEquiv (Process Name) where
  AlphaEquiv := Process.AlphaEquiv
  instEquiv := Equivalence.mk (fun _ => Process.AlphaEquiv.refl)
    (fun h => Process.AlphaEquiv.symm h) (fun h₁ h₂ => Process.AlphaEquiv.trans h₁ h₂)

/-- If p' = p.subst x y, then if q and p.subst x y are α-convertible, q and p' are α-convertible. -/
theorem Process.alpha_subst_from_eq [DecidableEq Name] [HasFresh Name]
  {p q p' : Process Name} (h : p' = p.subst x y) :
  AlphaEquiv q (p.subst x y) → AlphaEquiv q p'
:= by
  intro hsubst
  rw[h]
  exact hsubst


section Notations

/-- A motive can be converted to a process. -/
instance : Coe (Motive Name) (Process Name) where
  coe m := Process.motive m

/-- Notation for Prefix. -/
notation:65 a:65 "("x")" => Prefix.recv a x
notation:65 a:65 "⟨"x"⟩" => Prefix.send a x
notation:65 "["x:65"="y:65"]"π => Prefix.guard x y π

/-- Notations for Process. -/
notation:65 p:65 "‖" q:65 => Process.par p q
notation:65 "(ν"z:65")" p:65 => Process.res z p
notation:65 "!"a:65"("x")" p:65 => Process.bang a x p

/-- Notations for Motives. -/
notation:65 "𝐨" => Motive.nil
notation:65 π:65 "∘"p => Motive.pre π p
notation:65 m₁ "+" m₂ => Motive.sum m₁ m₂
notation:65 m"ₘ" => Process.motive m

end Notations

end Cslib.PiCal
