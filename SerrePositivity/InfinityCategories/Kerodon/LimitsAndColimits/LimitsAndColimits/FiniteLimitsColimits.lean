module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite

/-! General declarations moved verbatim from their original modules.

対応節は Kerodon 7.1（Tag 02H1）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial

/-- 概要：全ての有限単体集合の図式が極限を持つ。
方針：有限形状の図式に A2 の HasLimit を課す。
規約：形状と対象は同じ単体集合の宇宙。使われ方：HA Proposition 1.1.3.4 の十分条件。 -/
class HasFiniteLimits (X : SSet.{u}) : Prop where
  hasLimit {K : SSet.{u}} [K.Finite] (p : K ⟶ X) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p


/-- 概要：全ての有限単体集合の図式が余極限を持つ。
方針：有限形状の図式に coslice による HasColimit を課す。
規約：形状と対象は同じ宇宙。使われ方：HA Proposition 1.1.3.4 の十分条件。 -/
class HasFiniteColimits (X : SSet.{u}) : Prop where
  hasColimit {K : SSet.{u}} [K.Finite] (p : K ⟶ X) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p


end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
