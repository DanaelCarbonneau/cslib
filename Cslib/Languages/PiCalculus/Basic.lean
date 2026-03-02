/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
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
(nil or a constant).

## References

* [R. Milner, *A Calculus of Communicating Systems*][Milner80]
* [D. Sangiorgi, *Introduction to Bisimulation and Coinduction*][Sangiorgi2011]
-/

namespace Cslib.PiCal

universe u v

/-- Actions. -/
inductive Act (Name : Type u) : Type u where
  | name (a : Name) (b : Name)
  | coname (a : Name) (b : Name)
  | coname_open (a : Name) (b : Name)
  | τ
deriving DecidableEq

def Act.mem (μ : Act Name) (n : Name) : Prop :=
  match μ with
  | name a b | coname a b | coname_open a b => a = n ∧ b = n
  | τ => False

instance : Membership Name (Act Name) where
  mem := Act.mem


/- Communicating canals -/

inductive Chan (Name : Type u) : Type u where
  | send (a : Name) (x : Name) -- a(x)
  | recv (a : Name) (x : Name) -- a'⟨x⟩
deriving DecidableEq

def Chan.subst [DecidableEq Name] (μ : Chan Name) (x v : Name) : Chan Name :=
  match μ with
  | send a x' =>
    if a = x then
      (if x' = x then send v v else send v x')
    else
      (if x' = x then send a v else send a x')
  | recv a x' => if a = x then recv v x' else recv a x'

def Chan.Bounds? [DecidableEq Name] (μ : Chan Name) (x : Name) : Bool :=
  match μ with
  | recv _ x' => x = x'
  | _ => false

def Chan.bv [DecidableEq Name] (μ : Chan Name) : Finset Name :=
  match μ with
  | send _ _ => ∅
  | recv _ x => {x}

def Chan.fv [DecidableEq Name] (μ : Chan Name) : Finset Name :=
  match μ with
  | send a x => {a,x}
  | recv a _ => {a}



/-- Processes. -/
inductive Process (Name : Type u) (Constant : Type v) : Type (max u v) where
  | nil
  | pre (μ : Chan Name) (p : Process Name Constant)
  | par (p q : Process Name Constant)
  | choice (p q : Process Name Constant)
  | res (a : Name) (p : Process Name Constant) -- c'est le nu !
  | const (c : Constant)
  | bang (a x : Name)  (p : Process Name Constant) --!a(x).P
deriving DecidableEq


/-- Free variables of the process -/
def Process.fv [DecidableEq Name] : Process Name Constant → Finset Name
  | nil | const _ => ∅
  | pre μ p => (p.fv  \ μ.bv ∪ μ.fv) -- all of the variables in p except the ones bounded in μ
  | par p q | choice p q => p.fv ∪ q.fv
  | res a p => p.fv.erase a
  | bang a x p => ({a} ∪ p.fv).erase x

/-- Bounded variables of the process -/
def Process.bv [DecidableEq Name] : Process Name Constant → Finset Name
  | nil | const _ => ∅
  | pre μ  p => p.bv ∪ μ.bv
  | par p q | choice p q => p.bv ∪ q.bv
  | res a p => {a} ∪ p.bv
  | bang _ x p => {x} ∪ p.bv

/- Variables (free and bound) in a process -/
def Process.vars [DecidableEq Name] (p : Process Name Constant) : Finset Name :=
  p.fv ∪ p.bv



def Process.subst [HasFresh Name]
  [DecidableEq Name] (p : Process Name Constant) (x v : Name)
  : Process Name Constant :=
match p with
| .nil => nil
| .pre μ p =>
  if μ.Bounds? x then -- x is not a free variable in p, we stop the substitution
    pre (μ.subst x v) p
  else -- x is a free variable in p, we continue the substitution
    pre (μ.subst x v) (p.subst x v)
| .par p q => par (p.subst x v) (q.subst x v)
| .choice p q => choice (p.subst x v) (q.subst x v)
| .res a p' => -- si a = v, alpha convertir !
  if a = x then res a p' --
  else
  if a = v then
    let a' := HasFresh.fresh p.vars
    res a' (p'.subst a a')
  else res a (p'.subst x v)
| .const c => const c
| .bang a x' p =>
  if a = x then
    if x = x' then -- x est lié !
      bang v x' p
    else
      bang v x (p.subst x v)
  else
    if x = x' then -- x est lié !
      bang a v p
    else
      bang a v (p.subst x v)

instance instSubstitutionProcess [DecidableEq Name] [HasFresh Name] :
    HasSubstitution (Process Name Constant) Name Name where
  subst := Process.subst




notation:65 p:65 "‖" q:65 => Process.par p q
notation:65 p:65 "+" q:65 => Process.choice p q
notation:65 a:65 "(" x ")·" p => Process.pre  (Chan.recv a x) p
notation:65 a:65 "-⟨" x "⟩·" p => Process.pre  (Chan.send a x) p
notation:65 "(ν" x ")" p => Process.res x p
notation:65 "!" a "("x")·"p => Process.bang a x p
notation:65 "∘" => Process.nil



namespace Act

/-- An action is visible if it a name or a coname. -/
@[scoped grind]
inductive IsVisible : Act Name → Prop where
  | name : IsVisible (Act.name a b)
  | coname : IsVisible (Act.coname a b)
  | coname_open : IsVisible (Act.coname_open a b)

/-- If an action is visible, it is not `τ`. -/
@[scoped grind →, simp]
theorem isVisible_neq_τ {μ : Act Name} (h : μ.IsVisible) : μ ≠ Act.τ := by
  cases μ <;> grind

/-- Checks that an action is the coaction of another. -/
@[scoped grind]
inductive Co {Name : Type u} : Act Name → Act Name → Prop where
  | nc : Co (name a b) (coname a c)
  | cn : Co (coname a b) (name a c)
  | nco : Co (name a b) (coname_open a c)
  | cno : Co (coname_open a c) (name a b)

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
  | name a _, coname b _ | coname a _, name b _ | coname_open a _, name b _
    | name a _, coname_open b _=> a = b
  | _, _ => false

theorem isCo_iff [DecidableEq Name] {μ μ' : Act Name} : isCo μ μ' ↔ Co μ μ' := by
  grind [cases Act]

/-- `Act.Co` is decidable if `Name` equality is decidable. -/
instance [DecidableEq Name] {μ μ' : Act Name} : Decidable (Co μ μ') :=
  decidable_of_decidable_of_iff isCo_iff





end Act

instance : ToString (Chan String) where
  toString c :=
  match c with
  | .send a x => s!"{a}-⟨{x}⟩"
  | .recv a x => s!"{a}({x})"

instance : ToString (Chan Nat) where
  toString c :=
  match c with
  | .send a x => s!"{a}-⟨{x}⟩"
  | .recv a x => s!"{a}({x})"


def Process.toString (p : Process String String) :=
match p with
| .nil => "0"
| .pre μ p => s!"{μ}.{p.toString}"
| .par p q => s!"{p.toString} | {q.toString}"
| .choice p q => s!"{p.toString}+{q.toString}"
| .res a p => s!"(ν {a}) {p.toString}}"
| .const c => c
| .bang a x p => s!"!{a}({x}). {p.toString}"


def Process.toString' (p : Process Nat Nat) :=
match p with
| .nil => "0"
| .pre μ p => s!"{μ}.{p.toString'}"
| .par p q => s!"{p.toString'} | {q.toString'}"
| .choice p q => s!"{p.toString'}+{q.toString'}"
| .res a p => s!"(ν {a}) {p.toString'}}"
| .const c => s!"{c}"
| .bang a x p => s!"!{a}({x}). {p.toString'}"


instance : ToString (Process String String) where
toString := Process.toString

instance : ToString (Process Nat Nat) where
toString := Process.toString'
open Process



def pEx (a b x y : Name) : Process Name Constant := -- a(x).x'⟨y⟩ | a'⟨b⟩.nil
  par (pre (Chan.recv a x) (pre (Chan.send x y) nil )) (pre (Chan.send a b) nil)
def pEx' (a b x y : Name) : Process Name Constant :=
  (a(x)·x-⟨y⟩·∘ )‖(a-⟨b⟩·∘ )

example (a b x y : Name) : (pEx a b x y (Constant := Constant))= pEx' a b x y :=
by
  unfold pEx pEx'
  rfl

#eval pEx "a" "b" "x" "y" (Constant := String)
#eval (pre (Chan.recv 1 2) (pre (Chan.send 2 3) nil ) (Constant := ℕ)).subst  2 4


#eval (pEx 1 2 3 4  (Constant := Nat))[4 :=5]

variable {Name : Type u} [DecidableEq Name] {Constant : Type v}
  {defs : Constant → PiCal.Process Name Constant → Prop}


#eval (Chan.recv "a" "x").Bounds? "z"
--#eval (pre (Chan.send "x" "y") nil  (Constant := String)).subst "y" "z"
#eval (Chan.send "x" "y").Bounds? "y"
end Cslib.PiCal

#check (· +1)
