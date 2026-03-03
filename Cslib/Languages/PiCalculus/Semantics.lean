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

-/

namespace Cslib

namespace PiCal

open Process





/-- The transition relation for PiCal.  -/
@[lts PiCal.lts]
inductive Tr [DecidableEq Name] [HasFresh Name] : Process Name Constant → Act Name → Process Name Constant → Prop
where
  | parL : Tr p μ p' → Tr (par p q) μ (par p' q)
  | parR : Tr q μ q' → Tr (par p q) μ (par p q')
  | choiceL : Tr p μ p' → Tr (choice p q) μ p'
  | choiceR : Tr q μ q' → Tr (choice p q) μ q'
  | com :
    μ.Co μ' → Tr p μ p' → Tr q μ' q' → Tr (par p q) Act.τ (par p' q')
  | out : Tr (pre (Chan.send a x) p) (Act.coname a x) p
  | inp : Tr (pre (Chan.recv a x) p) (Act.name a v) (p[x := v])
  | res : a ∉ μ → Tr p μ p' →  Tr (res a p) μ ( res a p')
  | opn : Tr p (Act.coname a b) p' → Tr (res b p) (Act.coname_open a b) p'

  | clsL : Tr p (Act.name a b) p' → Tr q (Act.coname_open a b) q' →
    Tr (par p q) τ (res b ( par p' q'))
  | clsR : Tr p (Act.coname_open a b) p' → Tr q (Act.name a b) q' →
    Tr (par p q) τ (res b (par p' q'))

  | rpl : Tr (bang a x p) (Act.name a v) (par (bang a x p) (p[x := v]))






instance : HasTau (Act Name) where
  τ := Act.τ




end PiCal


end Cslib
