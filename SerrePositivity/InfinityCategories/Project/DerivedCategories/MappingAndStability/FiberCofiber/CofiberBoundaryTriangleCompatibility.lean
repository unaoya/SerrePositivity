module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.CofiberBoundaryLegCompatibility
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanTwoPrefixTransport

/-! # 標準 cofiber 境界の三角形側の微分条件

概要：型付き三角形残差の微分を共通の後続・A 側右辺と各脚の右辺で表す。
方針：生の三角形 Bianchi を Hom 座標へ移し、標準ホモトピーを代入する。
規約：任意の非有界複体。使われ方：D7 の六成分線形系の最後の整合条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {A B C : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- 概要：r_AB の微分は標準ホモトピーと二つの脚側右辺の三項の符号付き和。
方針：零未知データの三角形 Bianchi に標準余錐の各成分を代入する。
規約：右側では零ホモトピーの項は消える。使われ方：六成分線形系の整合条件。 -/
lemma cofiberBoundaryRhsAB_differential {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberCocone f g)) :
    δ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n + 1)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAB f g b hb) =
      ((n : ℤ) + 1).negOnePow •
        ((mappingCone.inl (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.cofiberDifference f g)).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhs0 f g b hb)
          (by omega) + _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsA f g b hb -
          (Cochain.ofHom f).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsB f g b hb)
            (zero_add (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n + 1))) := by
  have H := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.span_twoPrefix_differential_of_heq (A := S) (D := Complex S)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftBase f g b)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftData_equation (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b) _)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData_unknownHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_left_A f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_left_apex f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_left_B f g b hb) rfl
    (by dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhs0 f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsB f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsA f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAB f g b hb)
    (Cochain.ofHom f) (mappingCone.inl (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.cofiberDifference f g))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhs0_heq f g b hb).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsB_heq f g b hb).symm
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftBase f g b).spanTwoPrefixFirstRhs_heq).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsA_heq f g b hb).symm)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAB_heq f g b hb).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_left_span_heq f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_left_homotopy_heq f g b hb)
  change δ _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAB f g b hb) = _ at H
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.complex_compose, Cochain.zero_comp, zero_add] using H

/-- 概要：r_AC の微分は標準ホモトピーと二つの脚側右辺の三項の符号付き和。
方針：零未知データの三角形 Bianchi に標準余錐の各成分を代入する。
規約：右側では零ホモトピーの項は消える。使われ方：六成分線形系の整合条件。 -/
lemma cofiberBoundaryRhsAC_differential {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberCocone f g)) :
    δ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n + 1)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAC f g b hb) =
      ((n : ℤ) + 1).negOnePow •
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsA f g b hb -
          (Cochain.ofHom g).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsC f g b hb)
            (zero_add (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n + 1))) := by
  have H := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.span_twoPrefix_differential_of_heq (A := S) (D := Complex S)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightBase f g b)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightData_equation (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b) _)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData_unknownHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_right_A f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_right_apex f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_right_C f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryTarget_right_eq f g b)
    (by dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhs0 f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsC f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsA f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAC f g b hb)
    (Cochain.ofHom g) ((0 : Cochain A (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutCofiber f g) (-1)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhs0_heq_right f g b hb).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsC_heq f g b hb).symm
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightBase f g b).spanTwoPrefixFirstRhs_heq).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsA_heq_right f g b hb).symm)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAC_heq f g b hb).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_right_span_heq f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_right_homotopy_heq f g b hb)
  change δ _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAC f g b hb) = _ at H
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.complex_compose, Cochain.zero_comp, zero_add] using H

end SerrePositivity.InfinityCategories.Project.DerivedCategories
