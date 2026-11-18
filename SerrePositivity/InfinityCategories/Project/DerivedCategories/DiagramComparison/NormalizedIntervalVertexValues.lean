module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedIntervalCycleData
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedHomZeroRawEvaluation
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.TruncationZeroCyclesInclusion
/-!
概要：指定正規化区間の零次生成元での実評価。
方針：既存のsmart切断Homの零次回収式で同じ値を戻す。
規約：A06の両端評価の証明分割。生成元・包含・単体を保持する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex AlgebraicTopology
open _root_.SerrePositivity.ComplexLimits
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]
/-- 指定正規化区間の同じ頂点生成元。 -/
def normalizedIntervalVertexGenerator (ε : Fin 2) :
    ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj ⦋1⦌)).X 0 :=
  let W := (SerrePositivity.EInfinity.BarrattEccles.linearization A).obj
    (SSet.stdSimplex.obj ⦋1⦌)
  (((normalizedMooreComplex (ModuleCat A)).obj W).extendXIso ComplexShape.embeddingDownNat
    (show ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) from rfl)).inv
      ((_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso W).inv (ModuleCat.freeMk (ULift.up
        (SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋1⦌ ε)))))
/-- 同じ区間写像の頂点生成元での値。 -/
theorem normalizedIntervalCochainMapOfBoundary_vertex
    (H : CochainComplex (ModuleCat.{u} A) ℤ)
    (x y : H.X 0) (hx : H.d 0 1 x = 0) (hy : H.d 0 1 y = 0)
    (w : H.X (-1)) (hw : H.d (-1) 0 w = y - x) (ε : Fin 2) :
    (normalizedIntervalCochainMapOfBoundary A H x y hx hy w hw).f 0
      (normalizedIntervalVertexGenerator A ε) = intervalVertexValue x y ε := by
  let W := (SerrePositivity.EInfinity.BarrattEccles.linearization A).obj
    (SSet.stdSimplex.obj ⦋1⦌)
  let a := SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋1⦌ ε)
  have h := ConcreteCategory.congr_hom
    (_root_.SerrePositivity.ComplexLimits.normalizedChainsTruncationHomEquiv_zero A (SSet.stdSimplex.obj ⦋1⦌) H
      (normalizedIntervalCochainMapOfBoundary A H x y hx hy w hw))
    ((_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso W).inv (ModuleCat.freeMk (ULift.up a)))
  dsimp only [normalizedIntervalCochainMapOfBoundary, normalizedIntervalCochainMap] at h
  rw [Equiv.apply_symm_apply] at h
  simp only [ModuleCat.comp_apply] at h
  rw [_root_.SerrePositivity.ComplexLimits.truncationExtendedZeroInclusion_cycles] at h
  dsimp only [intervalNormalizedChainMap] at h
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at h
  change H.iCycles 0 ((H.truncLE'XIsoCycles (ComplexShape.embeddingUpIntLE 0)
    (by simp) ((ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).mpr rfl)).hom
    (intervalVertexEvaluation A _ (intervalTruncCycle A H x hx)
      (intervalTruncCycle A H y hy)
      ((_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso W).hom ((_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso W).inv
        (ModuleCat.freeMk (ULift.up a)))))) = _ at h
  rw [Iso.inv_hom_id_apply] at h
  dsimp only [intervalVertexEvaluation] at h
  erw [ModuleCat.freeDesc_apply] at h
  change H.iCycles 0 ((H.truncLE'XIsoCycles (ComplexShape.embeddingUpIntLE 0)
    (by simp) ((ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).mpr rfl)).hom
    (intervalVertexValue (intervalTruncCycle A H x hx) (intervalTruncCycle A H y hy) ε)) = _ at h
  calc
    _ = H.iCycles 0 ((H.truncLE'XIsoCycles (ComplexShape.embeddingUpIntLE 0)
      (by simp) ((ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).mpr rfl)).hom
      (intervalVertexValue (intervalTruncCycle A H x hx) (intervalTruncCycle A H y hy) ε)) := h.symm
    _ = _ := by
      by_cases he : ε = 0
      · simp only [intervalVertexValue, he, ite_true]
        exact intervalTruncCycle_value A H x hx
      · simp only [intervalVertexValue, he, ite_false]
        exact intervalTruncCycle_value A H y hy
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
