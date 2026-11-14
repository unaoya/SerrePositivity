module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedIntervalChainNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedIntervalTruncationNaturality
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedHomTargetNaturality
/-!
概要：同じ正規化区間からのコチェイン評価は全標的射に自然。
方針：smart切断Homの標的自然性と同じ鎖評価の自然性を合成する。
規約：A06自然性の証明分割。元の区間写像自身の等式。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex CochainComplex
open SerrePositivity.EInfinity.ComplexLimits
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]
/-- 閉零次値と境界による同じコチェイン区間評価の自然性。 -/
theorem normalizedIntervalCochainMapOfBoundary_postcomp
    {H H' : CochainComplex (ModuleCat.{u} A) ℤ} (q : H ⟶ H')
    (x y : H.X 0) (hx : H.d 0 1 x = 0) (hy : H.d 0 1 y = 0)
    (w : H.X (-1)) (hw : H.d (-1) 0 w = y - x)
    (hx' : H'.d 0 1 (q.f 0 x) = 0) (hy' : H'.d 0 1 (q.f 0 y) = 0)
    (hw' : H'.d (-1) 0 (q.f (-1) w) = q.f 0 y - q.f 0 x) :
    normalizedIntervalCochainMapOfBoundary A H x y hx hy w hw ≫ q =
      normalizedIntervalCochainMapOfBoundary A H' (q.f 0 x) (q.f 0 y) hx' hy'
        (q.f (-1) w) hw' := by
  let tq := truncLE'Map q (ComplexShape.embeddingUpIntLE 0)
  have ht : (H'.truncLE' (ComplexShape.embeddingUpIntLE 0)).d 1 0
      (tq.f 1 (intervalTruncEdge A H w)) =
      tq.f 0 (intervalTruncCycle A H y hy) - tq.f 0 (intervalTruncCycle A H x hx) := by
    have hc := ConcreteCategory.congr_hom (tq.comm 1 0) (intervalTruncEdge A H w)
    simp only [ModuleCat.comp_apply] at hc
    rw [intervalTrunc_boundary A H x y hx hy w hw, map_sub] at hc
    exact hc
  have hr := intervalNormalizedChainMap_postcomp A tq
    (intervalTruncCycle A H x hx) (intervalTruncCycle A H y hy) (intervalTruncEdge A H w)
    (intervalTrunc_boundary A H x y hx hy w hw) ht
  dsimp only [tq] at hr
  simp only [intervalTruncCycle_naturality A q x hx hx',
    intervalTruncCycle_naturality A q y hy hy', intervalTruncEdge_naturality] at hr
  apply (normalizedChainsTruncationHomEquiv A (SSet.stdSimplex.obj ⦋1⦌) H').injective
  rw [normalizedChainsTruncationHomEquiv_postcomp]
  dsimp only [normalizedIntervalCochainMapOfBoundary, normalizedIntervalCochainMap]
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact hr
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
