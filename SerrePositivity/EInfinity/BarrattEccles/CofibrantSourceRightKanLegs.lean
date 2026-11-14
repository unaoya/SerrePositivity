module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRightKanCanonical
public import SerrePositivity.EInfinity.FrameHom.FrameAugmentationLimitLegs
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.ConeLegRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightConstantFamily

/-!
# 元の実右 Kan 極限錐の frame 上の全脚

概要：任意の反転関手の実右 Kan 極限錐を制限し、同じ全脚の可逆性を得る。
方針：元の次数比較への cofinal 制限を同じ frame 図式へ厳密に戻す。
規約：元の極限錐と元の全次数を保持する。
使われ方：元の実右 Kan 単位の全成分の可逆性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet SimplicialLocalization
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : CofibrantAlgebra A)

lemma cofibrantSourceFrameAugmentation_image_invertible
    {E : SSet.{u + 1}} [Quasicategory E]
    (F : nerve (cofibrantAlgebraRelativeCategory A).category ⟶ E)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (weakNerveEdges (cofibrantAlgebraRelativeCategory A)))
    (n : AsSmall.{u + 1} SimplexCategory) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk
      ((cofibrantDKSourceFrameAugmentation A X).app n)).map F).toTruncated := by
  have hw := hF (show ComposableArrows.mk₁ ((cofibrantDKSourceFrameAugmentation A X).app n) ∈
      weakNerveEdges (cofibrantAlgebraRelativeCategory A) from
    ⟨_, _, _, cofibrantDKSourceFrameAugmentation_weak A X n, rfl⟩)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (ComposableArrows.mk₁ ((cofibrantDKSourceFrameAugmentation A X).app n))).map
      ((truncation 2).map F)) at hw
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (ComposableArrows.mk₁ ((cofibrantDKSourceFrameAugmentation A X).app n))).map
      ((truncation 2).map F))
    (f := ((nerve.edgeMk ((cofibrantDKSourceFrameAugmentation A X).app n)).map F).toTruncated)
    rfl).mp hw

lemma cofibrantSourceRightKanLimitCone_leg_isInvertible
    {E : SSet.{u + 1}} [Quasicategory E]
    (F : nerve (cofibrantAlgebraRelativeCategory A).category ⟶ E)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (weakNerveEdges (cofibrantAlgebraRelativeCategory A)))
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram
      (hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)) F
      (cofibrantHammockVertex A X))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c)
    (i : (nerve (AsSmall.{u + 1} SimplexCategory)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c
      ((cofibrantSourceFrameRightKanMap A X).app (Opposite.op ⦋0⦌) i)) := by
  let u := cofibrantSourceFrameRightKanMap A X
  have hu := cofibrantSourceFrameRightKanMap_isLeftCofinal A X
  have he := cofibrantSourceFrameRightKanMap_diagram A X F
  let d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap (cofibrantDKSourceFrame A X) ≫ F) :=
    ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c u).val, (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c u).property.trans he⟩
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsLimitCone_congr he (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c u) d rfl).mp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLimitCone_iff_restrict_of_leftCofinal u hu _ c).mp hc)
  have h := FrameHom.FrameArrows.augmentationLimitCone_leg_isInvertible
    (cofibrantDKSourceFrame A X) (cofibrantDKSourceFrameAugmentation A X) F
    (cofibrantSourceFrameAugmentation_image_invertible A X F hF)
    sourceFrameIndex_weaklyContractible d hd i
  have he' : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg d i).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c (u.app (Opposite.op ⦋0⦌) i)).edge :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.nativeConeLeg_restrict_edge c u i
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he').mp h

end SerrePositivity.EInfinity.BarrattEccles
