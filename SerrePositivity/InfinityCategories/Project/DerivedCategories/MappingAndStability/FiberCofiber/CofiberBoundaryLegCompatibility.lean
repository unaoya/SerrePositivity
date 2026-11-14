module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.CofiberBoundarySharedResiduals
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanOnePrefixTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Checks

/-! # 標準 cofiber 境界の脚側の微分条件

概要：型付き残差の微分は標準包含・対角と後続右辺の合成に符号を掛けた式となる。
方針：生の Bianchi を対象・次数・各成分の異種等号に沿って移す。
規約：任意の非有界複体。使われ方：D7 の六成分線形系の脚側条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {A B C : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- 概要：r_B の微分は標準射との合成に (-1)^(n+1) を掛けた式。
方針：零未知データの脚側 Bianchi を標準 cofiber の Hom 座標へ移す。
規約：最初の頂点に標準余錐を指定する。使われ方：六成分線形系の整合条件。 -/
lemma cofiberBoundaryRhsB_differential {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberCocone f g)) :
    δ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n + 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n + 1 + 1)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsB f g b hb) =
      ((n : ℤ) + 1).negOnePow • (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionB f g)).comp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhs0 f g b hb) (zero_add (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n + 1 + 1)) := by
  have H := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SimplexData.span_onePrefix_differential_of_heq (A := S) (D := Complex S)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftBase f g b)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftData_equation (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b) _)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData_suffixHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_left_B f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_left_apex f g b hb) rfl rfl
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhs0 f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsB f g b hb)
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionB f g))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhs0_heq f g b hb).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsB_heq f g b hb).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_left_inclusion_heq f g b hb)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.complex_compose] at H
  exact H

/-- 概要：r_C の微分は標準射との合成に (-1)^(n+1) を掛けた式。
方針：零未知データの脚側 Bianchi を標準 cofiber の Hom 座標へ移す。
規約：最初の頂点に標準余錐を指定する。使われ方：六成分線形系の整合条件。 -/
lemma cofiberBoundaryRhsC_differential {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberCocone f g)) :
    δ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n + 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n + 1 + 1)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsC f g b hb) =
      ((n : ℤ) + 1).negOnePow • (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionC f g)).comp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhs0 f g b hb) (zero_add (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n + 1 + 1)) := by
  have H := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SimplexData.span_onePrefix_differential_of_heq (A := S) (D := Complex S)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightBase f g b)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightData_equation (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b) _)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData_suffixHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_right_C f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_right_apex f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryTarget_right_eq f g b) rfl
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhs0 f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsC f g b hb)
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionC f g))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhs0_heq_right f g b hb).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsC_heq f g b hb).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_right_inclusion_heq f g b hb)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.complex_compose] at H
  exact H

/-- 概要：r_A の微分は標準射との合成に (-1)^(n+1) を掛けた式。
方針：零未知データの脚側 Bianchi を標準 cofiber の Hom 座標へ移す。
規約：最初の頂点に標準余錐を指定する。使われ方：六成分線形系の整合条件。 -/
lemma cofiberBoundaryRhsA_differential {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberCocone f g)) :
    δ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n + 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n + 1 + 1)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsA f g b hb) =
      ((n : ℤ) + 1).negOnePow • (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutDiagonal f g)).comp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhs0 f g b hb) (zero_add (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n + 1 + 1)) := by
  have H := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SimplexData.span_onePrefix_differential_of_heq (A := S) (D := Complex S)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftBase f g b)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftData_equation (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b) _)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData_suffixHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b))
    (0) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_left_A f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_left_apex f g b hb) rfl rfl
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhs0 f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsA f g b hb)
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutDiagonal f g))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhs0_heq f g b hb).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsA_heq f g b hb).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_left_diagonal_heq f g b hb)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.complex_compose] at H
  exact H

end SerrePositivity.InfinityCategories.Project.DerivedCategories
