module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeLimitConeProjections
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeLimitConeCommutativity
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeComparisonPath
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.KanIntervalConePathCompatibility
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CospanFunctorIsoComposition

/-!
概要：余極限後の極限錐の二脚の指定比較は、元の native 指定 path と整合する。
方針：元の全錐円柱と区間錐の整合を合成し、元の二射影・指定円柱へ厳密に戻す。
規約：元の指定値を保持。使われ方：一般 coherent filtered 図式の引き戻し交換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B] [IsFilteredInfinity B]
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)
  (hc : ∀ b, IsLimitCone (coherentCospanConePointwiseCone F X Y Z C b))
local notation "f" => coherentCospanNativeLeftKanMap F X Y Z C
local notation "g" => coherentCospanNativeRightKanMap F X Y Z C
local notation "n" => coherentCospanConeNativeComparison F X Y Z C
local notation "left" => AsSmall.up.obj WalkingCospan.left
local notation "right" => AsSmall.up.obj WalkingCospan.right

/-- 元の native 二脚と指定 path を保つ、余極限後の極限錐の可換性の整合式。 -/
lemma coherentCospanNativeLimitCone_projection_commutativity :
    (coherentCospanNativeLimitConeFstIso F X Y Z C hc).postcomp f ≪≫
      coherentCospanConeNativePathDownIso F X Y Z C =
    coherentCospanNativeLimitConeNativeCommutativity F X Y Z C hc ≪≫
      (coherentCospanNativeLimitConeSndIso F X Y Z C hc).postcomp g := by
  apply cospanFunctorIso_target_transport f g
    (coherentCospanNativeLimitConeLeftCompositeIso F X Y Z C hc)
    (coherentCospanNativeLimitConeRightCompositeIso F X Y Z C hc)
    (coherentCospanNativeLimitConeFstIso F X Y Z C hc)
    (coherentCospanNativeLimitConeSndIso F X Y Z C hc)
    (coherentCospanNativeLimitConeNativeCommutativity F X Y Z C hc)
    ((intervalPullbackPathIso f g).precomp n)
    (coherentCospanConeNativePathDownIso F X Y Z C)
    (coherentCospanConeNativeComparison_left F X Y Z C)
    (coherentCospanConeNativeComparison_right F X Y Z C)
    (functorIsoOfEq_heq _ _ _) (functorIsoOfEq_heq _ _ _)
    (coherentCospanNativeComparisonPathIso_heq F X Y Z C).symm
  exact cospanFunctorIso_compose n f g
    (coherentCospanNativeLimitConeLegIso F X Y Z C hc left)
    (coherentCospanNativeLimitConeLegIso F X Y Z C hc right)
    (intervalPullbackConeFstIso f g) (intervalPullbackConeSndIso f g)
    (coherentCospanNativeLimitConeNativeCommutativity F X Y Z C hc)
    (intervalPullbackConeNativeCommutativity f g) (intervalPullbackPathIso f g)
    (coherentCospanNativeLimitConeNativeCommutativity_comparison F X Y Z C hc)
    (intervalPullbackCone_projection_commutativity f g)

end SerrePositivity.InfinityCategories.F2
