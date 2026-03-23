/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init

public section

namespace Cslib

/-- Typeclass for the α-equivalence notation `x =α y`. -/
class HasAlphaEquiv (β : Type u) where
  /-- α-equivalence relation for type β. -/
  AlphaEquiv : β → β → Prop
  instEquiv : Equivalence AlphaEquiv

@[inherit_doc]
notation m:max " =α " n:max => HasAlphaEquiv.AlphaEquiv m n

instance [HasAlphaEquiv β] : Trans (HasAlphaEquiv.AlphaEquiv (β := β))
  HasAlphaEquiv.AlphaEquiv  HasAlphaEquiv.AlphaEquiv  where
trans := HasAlphaEquiv.instEquiv.trans


end Cslib
