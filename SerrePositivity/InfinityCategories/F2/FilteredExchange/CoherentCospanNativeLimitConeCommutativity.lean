module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeLimitConeLeg
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.KanIntervalConeNativeCommutativity
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CospanIsoCancellation

/-!
概要：余極限後の錐の native な可換性と元の区間錐の可換性を指定値で比較する。
方針：左右三角形に対する同じ脚比較の自然性から、共通の中心脚比較を消去する。
規約：元の全錐円柱・指定同型を保持。使われ方：元の native path との最終整合。
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

/-- 元の余極限後の錐の左右三角形からの指定可換同型。 -/
def coherentCospanNativeLimitConeNativeCommutativity :
    FunctorIso (coherentCospanNativeLimitConeKanLeg F X Y Z C hc left ≫ f)
      (coherentCospanNativeLimitConeKanLeg F X Y Z C hc right ≫ g) :=
  (coherentCospanNativeLimitConeTriangleIso F X Y Z C hc
    (AsSmall.up.map WalkingCospan.Hom.inl)).symm ≪≫
    coherentCospanNativeLimitConeTriangleIso F X Y Z C hc
      (AsSmall.up.map WalkingCospan.Hom.inr)

/-- 元の指定脚比較は、両錐の元の native 可換性に対して整合する。 -/
lemma coherentCospanNativeLimitConeNativeCommutativity_comparison :
    coherentCospanNativeLimitConeNativeCommutativity F X Y Z C hc ≪≫
      (coherentCospanNativeLimitConeLegIso F X Y Z C hc right).postcomp g =
    (coherentCospanNativeLimitConeLegIso F X Y Z C hc left).postcomp f ≪≫
      (intervalPullbackConeNativeCommutativity f g).precomp n := by
  have h := cospanIso_cancel
    (coherentCospanNativeLimitConeTriangleIso F X Y Z C hc
      (AsSmall.up.map WalkingCospan.Hom.inl))
    (coherentCospanNativeLimitConeTriangleIso F X Y Z C hc
      (AsSmall.up.map WalkingCospan.Hom.inr))
    ((coherentCospanNativeLimitConeLegIso F X Y Z C hc left).postcomp f)
    ((coherentCospanNativeLimitConeLegIso F X Y Z C hc right).postcomp g)
    (coherentCospanNativeLimitConeLegIso F X Y Z C hc (AsSmall.up.obj WalkingCospan.one))
    ((intervalPullbackConeTriangleIso f g (AsSmall.up.map WalkingCospan.Hom.inl)).precomp n)
    ((intervalPullbackConeTriangleIso f g (AsSmall.up.map WalkingCospan.Hom.inr)).precomp n)
    (coherentCospanNativeLimitConeLegIso_naturality F X Y Z C hc
      (AsSmall.up.map WalkingCospan.Hom.inl))
    (coherentCospanNativeLimitConeLegIso_naturality F X Y Z C hc
      (AsSmall.up.map WalkingCospan.Hom.inr))
  simpa only [coherentCospanNativeLimitConeNativeCommutativity,
    intervalPullbackConeNativeCommutativity, functorIso_precomp_trans,
    functorIso_precomp_symm, Iso.trans_assoc] using h

end SerrePositivity.InfinityCategories.F2
