module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberBoundaryRawComparison
public import SerrePositivity.InfinityCategories.DGNerve.CospanOneTailTransport
public import SerrePositivity.InfinityCategories.DGNerve.CospanTwoTailTransport

/-! # dg 加群の fiber の実境界の微分整合式

概要：実際の slice 境界の脚と二三角形の残差の微分を求める。
方針：生の Bianchi を対象・次数・射の異種等号に沿って移す。
規約：全 Hom end の通常順の合成。使われ方：β3 の二未知成分の実解。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D} {n : ℕ} (f : M ⟶ N)
variable (b : (SSet.boundary (n + 1) : SSet) ⟶
  sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
variable (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
  SSet.yonedaEquiv.symm (dgModuleFiberCone A D f))

/-- M 側の実残差の微分は射影と先頭残差の合成の負。 -/
lemma dgModuleFiberBoundaryRhsM_differential :
    differential A (dgModuleFiberBoundaryRhsM A D f b hb) =
      -compose A (dgModuleFiberProjectionElement A D f)
        (dgModuleFiberBoundaryRhs0 A D f b hb)
        (add_zero (dgModuleFiberBoundaryDegree n + 1 + 1)) := by
  exact SimplexData.cospan_oneTail_differential_of_heq (A := A) (D := RightModule A D)
    (dgModuleFiberBoundaryLeftBase A D f b)
    (dgModuleFiberBoundaryLeftBase_equation A D f b)
    (dgModuleFiberBoundaryLeftBase_prefixHom A D f b)
    (cospanFirstTail n) (cospanApex_lt_firstTail n)
    rfl (dgModuleFiberBoundary_left_apex A D f b hb)
    (dgModuleFiberBoundary_left_M A D f b hb) rfl
    (dgModuleFiberBoundaryRhs0 A D f b hb) (dgModuleFiberBoundaryRhsM A D f b hb)
    (dgModuleFiberProjectionElement A D f)
    (dgModuleFiberBoundaryRhs0_heq_raw A D f b hb).symm
    (dgModuleFiberBoundaryRhsM_heq_raw A D f b hb).symm
    (dgModuleFiberBoundary_left_projection_heq A D f b hb)

/-- 左三角形の実残差の微分は元の射と零ホモトピーによる接続項を持つ。 -/
lemma dgModuleFiberBoundaryRhsMN_differential :
    differential A (dgModuleFiberBoundaryRhsMN A D f b hb) =
      dgModuleFiberBoundaryRhsN A D f b hb -
        compose A (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val
          (dgModuleFiberBoundaryRhsM A D f b hb)
          (add_zero (dgModuleFiberBoundaryDegree n + 1)) -
        compose A (dgModuleFiberNullHomotopy A D f)
          (dgModuleFiberBoundaryRhs0 A D f b hb) (by omega) := by
  have h := SimplexData.cospan_twoTail_differential_of_heq
    (A := A) (D := RightModule A D) (dgModuleFiberBoundaryLeftBase A D f b)
    (dgModuleFiberBoundaryLeftBase_equation A D f b)
    (dgModuleFiberBoundaryLeftBase_unknownHom A D f b)
    rfl (dgModuleFiberBoundary_left_apex A D f b hb)
    (dgModuleFiberBoundary_left_M A D f b hb) (dgModuleFiberBoundary_left_N A D f b hb)
    (by dsimp only [dgModuleFiberBoundaryDegree]; omega)
    (dgModuleFiberBoundaryRhs0 A D f b hb) (dgModuleFiberBoundaryRhsM A D f b hb)
    (dgModuleFiberBoundaryRhsN A D f b hb) (dgModuleFiberBoundaryRhsMN A D f b hb)
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val
    (dgModuleFiberNullHomotopy A D f)
    (dgModuleFiberBoundaryRhs0_heq_raw A D f b hb).symm
    (dgModuleFiberBoundaryRhsM_heq_raw A D f b hb).symm
    (((dgModuleFiberBoundaryLeftBase A D f b).cospanTwoTailLastRhs_heq).trans
      (dgModuleFiberBoundaryRhsN_heq_raw A D f b hb).symm)
    (dgModuleFiberBoundaryRhsMN_heq_raw A D f b hb).symm
    (dgModuleFiberBoundary_left_cospan_heq A D f b hb)
    (dgModuleFiberBoundary_left_homotopy_heq A D f b hb)
  change differential (D := RightModule A D) A
    (dgModuleFiberBoundaryRhsMN A D f b hb) = _ at h
  rw [h]
  abel

/-- 零角側の実三角形残差の微分は共通の N 側残差。 -/
lemma dgModuleFiberBoundaryRhsZeroN_differential :
    differential A (dgModuleFiberBoundaryRhsZeroN A D f b hb) =
      dgModuleFiberBoundaryRhsN A D f b hb := by
  have h := SimplexData.cospan_twoTail_differential_of_heq
    (A := A) (D := RightModule A D) (dgModuleFiberBoundaryRightBase A D f b)
    (dgModuleFiberBoundaryRightBase_equation A D f b)
    (dgModuleFiberBoundaryRightBase_unknownHom A D f b)
    (dgModuleFiberBoundarySource_right_eq A D f b) (dgModuleFiberBoundary_right_apex A D f b hb)
    (dgModuleFiberBoundary_right_zero A D f b hb) (dgModuleFiberBoundary_right_N A D f b hb)
    (by dsimp only [dgModuleFiberBoundaryDegree]; omega)
    (dgModuleFiberBoundaryRhs0 A D f b hb) (dgModuleFiberBoundaryRhsZero A D f b hb)
    (dgModuleFiberBoundaryRhsN A D f b hb) (dgModuleFiberBoundaryRhsZeroN A D f b hb)
    (0 : GradedHom A (ForgetEnrichment.to (Complex A) (moduleZero A D))
      (ForgetEnrichment.to (Complex A) N) 0)
    (0 : GradedHom A (dgModuleFiber A D f) (ForgetEnrichment.to (Complex A) N) (-1))
    (dgModuleFiberBoundaryRhs0_heq_right A D f b hb).symm
    (dgModuleFiberBoundaryRhsZero_heq_raw A D f b hb).symm
    (((dgModuleFiberBoundaryRightBase A D f b).cospanTwoTailLastRhs_heq).trans
      (dgModuleFiberBoundaryRhsN_heq_right A D f b hb).symm)
    (dgModuleFiberBoundaryRhsZeroN_heq_raw A D f b hb).symm
    (dgModuleFiberBoundary_right_cospan_heq A D f b hb)
    (dgModuleFiberBoundary_right_homotopy_heq A D f b hb)
  change differential (D := RightModule A D) A
    (dgModuleFiberBoundaryRhsZeroN A D f b hb) = _ at h
  simpa only [zero_compose, sub_zero, zero_add, add_zero, neg_neg] using h

end SerrePositivity.InfinityCategories
