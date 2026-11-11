module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleConeBoundaryLegCompatibility
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanTwoPrefixTransport

/-! # 実 dg 加群 cone 境界の型付き残差の微分条件

概要：生の Bianchi から、標準包含とホモトピーを持つ全 Hom end の式を得る。
方針：端点・次数・低次成分の異種等号を使って式を輸送する。
規約：相対境界の最初の頂点を標準余錐に固定する。使われ方：β3 の明示的原始元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D} {n : ℕ}
variable (f : M ⟶ N)
variable (b : (SSet.boundary (n + 1) : SSet) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
variable (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f))

/-- AB 側の三角形の Bianchi を実際の Hom end の三項の式に移す。 -/
lemma dgModuleConeBoundaryRhsAB_differential :
    differential (D := RightModule A D) A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsAB A D f b hb) =
      ((n : ℤ) + 1).negOnePow •
        (compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhs0 A D f b hb) (moduleConeInlElement A D f)
          (show (-1) + (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n + 1 + 1) =
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n + 1 by omega) +
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsA A D f b hb -
          compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsB A D f b hb) (cycleFromUnit _
            (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val
            (zero_add (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n + 1))) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.span_twoPrefix_differential_of_heq (A := A) (D := RightModule A D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftBase A D f b)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftData_equation (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b) _)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData_unknownHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_left_A A D f b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_left_apex A D f b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_left_B A D f b hb) rfl
    (by dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhs0 A D f b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsB A D f b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsA A D f b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsAB A D f b hb)
    (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val (_root_.SerrePositivity.DifferentialGraded.moduleConeInlElement A D f)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhs0_heq A D f b hb).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsB_heq A D f b hb).symm
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftBase A D f b).spanTwoPrefixFirstRhs_heq).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsA_heq A D f b hb).symm)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsAB_heq A D f b hb).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_left_span_heq A D f b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_left_homotopy_heq A D f b hb)

/-- AC 側の三角形の Bianchi を実際の Hom end の三項の式に移す。 -/
lemma dgModuleConeBoundaryRhsAC_differential :
    differential (D := RightModule A D) A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsAC A D f b hb) =
      ((n : ℤ) + 1).negOnePow •
        (compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhs0 A D f b hb) (0 : GradedHom A (ForgetEnrichment.to
          (_root_.SerrePositivity.DifferentialGraded.Complex A) M) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) (-1))
          (show (-1) + (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n + 1 + 1) =
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n + 1 by omega) +
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsA A D f b hb -
          compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsC A D f b hb) (0 : GradedHom A (ForgetEnrichment.to
            (_root_.SerrePositivity.DifferentialGraded.Complex A) M) (_root_.SerrePositivity.DifferentialGraded.zeroModule A D) 0)
            (zero_add (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n + 1))) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.span_twoPrefix_differential_of_heq (A := A) (D := RightModule A D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightBase A D f b)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightData_equation (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b) _)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData_unknownHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_right_A A D f b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_right_apex A D f b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_right_C A D f b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryTarget_right_eq A D f b)
    (by dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhs0 A D f b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsC A D f b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsA A D f b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsAC A D f b hb)
    (0 : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M) (_root_.SerrePositivity.DifferentialGraded.zeroModule A D) 0) (0 : _root_.SerrePositivity.DifferentialGraded.GradedHom A
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) (-1))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhs0_heq_right A D f b hb).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsC_heq A D f b
      hb).symm
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightBase A D f b).spanTwoPrefixFirstRhs_heq).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsA_heq_right A D f b hb).symm)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsAC_heq A D f b hb).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_right_span_heq A D f b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_right_homotopy_heq A D f b hb)

/-- 零加群から出る脚側の実残差は全次数で零。 -/
lemma dgModuleConeBoundaryRhsC_eq_zero : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsC A D f b hb = 0 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedHom_eq_zero_of_closed_isZero_source (moduleZero_isZero A D) _

/-- 零側の三角形の微分式では二つの合成項が消える。 -/
lemma dgModuleConeBoundaryRhsAC_differential_zero :
    differential (D := RightModule A D) A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsAC A D f b hb) =
      ((n : ℤ) + 1).negOnePow • _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsA A D f b hb := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, zero_add, sub_zero] using
    dgModuleConeBoundaryRhsAC_differential A D f b hb

end SerrePositivity.InfinityCategories.Project.DerivedCategories
