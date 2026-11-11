module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableOpposite
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.HomotopyOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HomotopyBinaryCoproduct
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

/-! # 安定 ∞ 圏のホモトピー圏の二項積

概要：安定 ∞ 圏のホモトピー圏は二項積を持つ。
方針：反対 quasicategory の安定性と二項余積を、ホモトピー圏の反対との同値で移す。
規約：加法構造を仮定しない。使われ方：双積と前加法構造の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：安定 ∞ 圏のホモトピー圏は二項積を持つ。
方針：反対側の二項余積を圏同値で元のホモトピー圏の反対へ移して双対化する。
規約：元の X は安定な quasicategory。使われ方：h C の双積と加法構造。 -/
instance hasBinaryProducts_ho {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    HasBinaryProducts (hoFunctor.obj X) := by
  let : HasBinaryCoproducts (hoFunctor.obj X)ᵒᵖ :=
    Adjunction.hasColimitsOfShape_of_equivalence (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.homotopyOppositeEquivalence X).inverse
  exact hasProductsOfShape_of_opposite WalkingPair

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
