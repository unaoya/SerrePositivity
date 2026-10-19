module
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeBoundarySharedResiduals
public import SerrePositivity.InfinityCategories.Derived.SpanOnePrefixTransport
public import SerrePositivity.InfinityCategories.Derived.SpanTwoPrefixTransport
public import SerrePositivity.InfinityCategories.Derived.DGModuleZeroHom

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

/-- B 側の脚の Bianchi を全 Hom end の指定された座標へ移す。 -/
lemma dgModuleConeBoundaryRhsB_differential :
    differential (D := RightModule A D) A (dgModuleConeBoundaryRhsB A D f b hb) =
      ((n : ℤ) + 1).negOnePow • compose A (dgModuleConeBoundaryRhs0 A D f b hb)
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (moduleConeInr A D f))).val
          (zero_add (dgModuleConeBoundaryDegree n + 1 + 1)) := by
  exact SimplexData.span_onePrefix_differential_of_heq (A := A) (D := RightModule A D)
    (dgModuleConeBoundaryLeftBase A D f b)
    (spanBoundaryLeftData_equation (sliceUnderUncurry b) _)
    (spanBoundaryLeftZeroData_suffixHom (sliceUnderUncurry b))
    (spanSecondPrefix n) (spanSecondPrefix_lt_apex n)
    (dgModuleConeBoundary_left_B A D f b hb)
    (dgModuleConeBoundary_left_apex A D f b hb) rfl rfl
    (dgModuleConeBoundaryRhs0 A D f b hb) (dgModuleConeBoundaryRhsB A D f b hb)
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (moduleConeInr A D f))).val
    (dgModuleConeBoundaryRhs0_heq A D f b hb).symm (dgModuleConeBoundaryRhsB_heq A D f b hb).symm
    (dgModuleConeBoundary_left_inclusion_heq A D f b hb)

/-- C 側の脚の Bianchi を全 Hom end の指定された座標へ移す。 -/
lemma dgModuleConeBoundaryRhsC_differential :
    differential (D := RightModule A D) A (dgModuleConeBoundaryRhsC A D f b hb) =
      ((n : ℤ) + 1).negOnePow • compose A (dgModuleConeBoundaryRhs0 A D f b hb)
        (0 : GradedHom A (zeroModule A D) (ForgetEnrichment.to (Complex A) (moduleCone A D f))
          0) (zero_add (dgModuleConeBoundaryDegree n + 1 + 1)) := by
  exact SimplexData.span_onePrefix_differential_of_heq (A := A) (D := RightModule A D)
    (dgModuleConeBoundaryRightBase A D f b)
    (spanBoundaryRightData_equation (sliceUnderUncurry b) _)
    (spanBoundaryRightZeroData_suffixHom (sliceUnderUncurry b))
    (spanSecondPrefix n) (spanSecondPrefix_lt_apex n)
    (dgModuleConeBoundary_right_C A D f b hb)
    (dgModuleConeBoundary_right_apex A D f b hb) (dgModuleConeBoundaryTarget_right_eq A D f b) rfl
    (dgModuleConeBoundaryRhs0 A D f b hb) (dgModuleConeBoundaryRhsC A D f b hb)
    (0 : GradedHom A (zeroModule A D) (ForgetEnrichment.to (Complex A) (moduleCone A D f)) 0)
    (dgModuleConeBoundaryRhs0_heq_right A D f b hb).symm (dgModuleConeBoundaryRhsC_heq A D f b
      hb).symm
    (dgModuleConeBoundary_right_inclusion_heq A D f b hb)

/-- A 側の脚の Bianchi を全 Hom end の指定された座標へ移す。 -/
lemma dgModuleConeBoundaryRhsA_differential :
    differential (D := RightModule A D) A (dgModuleConeBoundaryRhsA A D f b hb) =
      ((n : ℤ) + 1).negOnePow • compose A (dgModuleConeBoundaryRhs0 A D f b hb)
        (0 : GradedHom A (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A)
          (moduleCone A D f)) 0) (zero_add (dgModuleConeBoundaryDegree n + 1 + 1)) := by
  exact SimplexData.span_onePrefix_differential_of_heq (A := A) (D := RightModule A D)
    (dgModuleConeBoundaryLeftBase A D f b)
    (spanBoundaryLeftData_equation (sliceUnderUncurry b) _)
    (spanBoundaryLeftZeroData_suffixHom (sliceUnderUncurry b))
    (0) (spanApex_pos n)
    (dgModuleConeBoundary_left_A A D f b hb)
    (dgModuleConeBoundary_left_apex A D f b hb) rfl rfl
    (dgModuleConeBoundaryRhs0 A D f b hb) (dgModuleConeBoundaryRhsA A D f b hb)
    (0 : GradedHom A (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A)
      (moduleCone A D f)) 0)
    (dgModuleConeBoundaryRhs0_heq A D f b hb).symm (dgModuleConeBoundaryRhsA_heq A D f b hb).symm
    (dgModuleConeBoundary_left_diagonal_heq A D f b hb)

end SerrePositivity.InfinityCategories
