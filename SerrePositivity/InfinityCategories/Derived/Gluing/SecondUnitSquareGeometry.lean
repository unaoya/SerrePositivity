module
public import SerrePositivity.InfinityCategories.Derived.Gluing.SlicePrismSquareSection
public import SerrePositivity.InfinityCategories.Derived.DGCompositionUnitCollapse
public import SerrePositivity.InfinityCategories.Core.StdSimplexProductMap
/-!
概要：第二単位の二時間の縮約は二つの時刻の最大値による一時間の切断である。
方針：各頂点の零・非零を分け、同じ終点を保持する縮約を合成する。
規約：全次数の順序写像の等式であり、境界だけへ制限しない。
使われ方：coherent 第二単位の正方形を σ₁ 退化三角形へ制限する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

def dgGluingUnitSquareMaxOrder : Fin 2 × Fin 2 →o Fin 2 where
  toFun p := max p.1 p.2
  monotone' _ _ h := max_le_max h.1 h.2

def dgGluingUnitSquareMax : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[1] :=
  stdSimplexProductMap dgGluingUnitSquareMaxOrder

lemma dgGluingUnitSquareMax_section :
    dgGluingTriangleSquareSection.{u} ≫ dgGluingUnitSquareMax =
      stdSimplex.σ (1 : Fin 2) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i <;> rfl

lemma dgGluingSecondUnit_prism_cut {n : ℕ}
    (s t : Fin (n + 1) →o Fin 2) :
    (dgCompositionUnitCollapse t).comp (coherentPrismCut s) =
      coherentPrismCut (s ⊔ t) := by
  apply OrderHom.ext
  funext i
  by_cases hs : s i = 0 <;> by_cases ht : t i = 0
  · simp only [OrderHom.comp_coe, Function.comp_apply, coherentPrismCut_zero s i hs,
      dgCompositionUnitCollapse_zero t i ht]
    apply (coherentPrismCut_zero (s ⊔ t) i (by simp [hs, ht])).symm
  · simp only [OrderHom.comp_coe, Function.comp_apply, coherentPrismCut_zero s i hs,
      dgCompositionUnitCollapse_one t i ht]
    apply (coherentPrismCut_one (s ⊔ t) i (by simpa [hs] using ht)).symm
  · simp only [OrderHom.comp_coe, Function.comp_apply, coherentPrismCut_one s i hs,
      dgCompositionUnitCollapse_last]
    apply (coherentPrismCut_one (s ⊔ t) i (by simpa [ht] using hs)).symm
  · simp only [OrderHom.comp_coe, Function.comp_apply, coherentPrismCut_one s i hs,
      dgCompositionUnitCollapse_last]
    apply (coherentPrismCut_one (s ⊔ t) i (by
      intro h
      exact hs (le_antisymm (le_sup_left.trans_eq h) (Fin.zero_le _)))).symm
end SerrePositivity.InfinityCategories
