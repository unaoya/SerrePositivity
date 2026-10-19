module
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeBoundaryLegCompatibility
public import SerrePositivity.InfinityCategories.Derived.SpanTwoPrefixTransport

/-! # 実 dg 加群 cone 境界の型付き残差の微分条件

概要：生の Bianchi から、標準包含とホモトピーを持つ全 Hom end の式を得る。
方針：端点・次数・低次成分の異種等号を使って式を輸送する。
規約：相対境界の最初の頂点を標準余錐に固定する。使われ方：β3 の明示的原始元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D} {n : ℕ}
variable (f : M ⟶ N)
variable (b : (SSet.boundary (n + 1) : SSet) ⟶ sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
variable (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f))

/-- AB 側の三角形の Bianchi を実際の Hom end の三項の式に移す。 -/
lemma dgModuleConeBoundaryRhsAB_differential :
    differential (D := RightModule A D) A (dgModuleConeBoundaryRhsAB A D f b hb) =
      ((n : ℤ) + 1).negOnePow •
        (compose A (dgModuleConeBoundaryRhs0 A D f b hb) (moduleConeInlElement A D f)
          (show (-1) + (dgModuleConeBoundaryDegree n + 1 + 1) =
            dgModuleConeBoundaryDegree n + 1 by omega) +
          dgModuleConeBoundaryRhsA A D f b hb -
          compose A (dgModuleConeBoundaryRhsB A D f b hb) (cycleFromUnit _
            (ForgetEnrichment.homTo (Complex A) f)).val
            (zero_add (dgModuleConeBoundaryDegree n + 1))) := by
  exact SimplexData.span_twoPrefix_differential_of_heq (A := A) (D := RightModule A D)
    (dgModuleConeBoundaryLeftBase A D f b)
    (spanBoundaryLeftData_equation (sliceUnderUncurry b) _)
    (spanBoundaryLeftZeroData_unknownHom (sliceUnderUncurry b))
    (dgModuleConeBoundary_left_A A D f b hb)
    (dgModuleConeBoundary_left_apex A D f b hb)
    (dgModuleConeBoundary_left_B A D f b hb) rfl
    (by dsimp only [dgModuleConeBoundaryDegree]; omega)
    (dgModuleConeBoundaryRhs0 A D f b hb) (dgModuleConeBoundaryRhsB A D f b hb)
    (dgModuleConeBoundaryRhsA A D f b hb) (dgModuleConeBoundaryRhsAB A D f b hb)
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val (moduleConeInlElement A D f)
    (dgModuleConeBoundaryRhs0_heq A D f b hb).symm (dgModuleConeBoundaryRhsB_heq A D f b hb).symm
    (((dgModuleConeBoundaryLeftBase A D f b).spanTwoPrefixFirstRhs_heq).trans
      (dgModuleConeBoundaryRhsA_heq A D f b hb).symm)
    (dgModuleConeBoundaryRhsAB_heq A D f b hb).symm
    (dgModuleConeBoundary_left_span_heq A D f b hb)
    (dgModuleConeBoundary_left_homotopy_heq A D f b hb)

/-- AC 側の三角形の Bianchi を実際の Hom end の三項の式に移す。 -/
lemma dgModuleConeBoundaryRhsAC_differential :
    differential (D := RightModule A D) A (dgModuleConeBoundaryRhsAC A D f b hb) =
      ((n : ℤ) + 1).negOnePow •
        (compose A (dgModuleConeBoundaryRhs0 A D f b hb) (0 : GradedHom A (ForgetEnrichment.to
          (Complex A) M) (ForgetEnrichment.to (Complex A) (moduleCone A D f)) (-1))
          (show (-1) + (dgModuleConeBoundaryDegree n + 1 + 1) =
            dgModuleConeBoundaryDegree n + 1 by omega) +
          dgModuleConeBoundaryRhsA A D f b hb -
          compose A (dgModuleConeBoundaryRhsC A D f b hb) (0 : GradedHom A (ForgetEnrichment.to
            (Complex A) M) (zeroModule A D) 0)
            (zero_add (dgModuleConeBoundaryDegree n + 1))) := by
  exact SimplexData.span_twoPrefix_differential_of_heq (A := A) (D := RightModule A D)
    (dgModuleConeBoundaryRightBase A D f b)
    (spanBoundaryRightData_equation (sliceUnderUncurry b) _)
    (spanBoundaryRightZeroData_unknownHom (sliceUnderUncurry b))
    (dgModuleConeBoundary_right_A A D f b hb)
    (dgModuleConeBoundary_right_apex A D f b hb)
    (dgModuleConeBoundary_right_C A D f b hb) (dgModuleConeBoundaryTarget_right_eq A D f b)
    (by dsimp only [dgModuleConeBoundaryDegree]; omega)
    (dgModuleConeBoundaryRhs0 A D f b hb) (dgModuleConeBoundaryRhsC A D f b hb)
    (dgModuleConeBoundaryRhsA A D f b hb) (dgModuleConeBoundaryRhsAC A D f b hb)
    (0 : GradedHom A (ForgetEnrichment.to (Complex A) M) (zeroModule A D) 0) (0 : GradedHom A
      (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) (moduleCone A D f)) (-1))
    (dgModuleConeBoundaryRhs0_heq_right A D f b hb).symm (dgModuleConeBoundaryRhsC_heq A D f b
      hb).symm
    (((dgModuleConeBoundaryRightBase A D f b).spanTwoPrefixFirstRhs_heq).trans
      (dgModuleConeBoundaryRhsA_heq_right A D f b hb).symm)
    (dgModuleConeBoundaryRhsAC_heq A D f b hb).symm
    (dgModuleConeBoundary_right_span_heq A D f b hb)
    (dgModuleConeBoundary_right_homotopy_heq A D f b hb)

/-- 零加群から出る脚側の実残差は全次数で零。 -/
lemma dgModuleConeBoundaryRhsC_eq_zero : dgModuleConeBoundaryRhsC A D f b hb = 0 :=
  dgGradedHom_eq_zero_of_closed_isZero_source (moduleZero_isZero A D) _

/-- 零側の三角形の微分式では二つの合成項が消える。 -/
lemma dgModuleConeBoundaryRhsAC_differential_zero :
    differential (D := RightModule A D) A (dgModuleConeBoundaryRhsAC A D f b hb) =
      ((n : ℤ) + 1).negOnePow • dgModuleConeBoundaryRhsA A D f b hb := by
  simpa only [compose_zero, zero_add, sub_zero] using
    dgModuleConeBoundaryRhsAC_differential A D f b hb

end SerrePositivity.InfinityCategories
