module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedIntervalCycleData
/-!
概要：区間の境界データをsmart切断へ送る操作の自然性。
方針：既存切断射の零次cycles公式と一次項公式を使う。
規約：A06自然性の証明分割。閉性の仮定を型に保持する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex CochainComplex
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]
/-- 閉零次値の切断への持ち上げは元の複体射で自然。 -/
theorem intervalTruncCycle_naturality {H H' : CochainComplex (ModuleCat.{u} A) ℤ}
    (q : H ⟶ H') (z : H.X 0) (hz : H.d 0 1 z = 0) (hz' : H'.d 0 1 (q.f 0 z) = 0) :
    (truncLE'Map q (ComplexShape.embeddingUpIntLE 0)).f 0 (intervalTruncCycle A H z hz) =
      intervalTruncCycle A H' (q.f 0 z) hz' := by
  let e0 := H'.truncLE'XIsoCycles (ComplexShape.embeddingUpIntLE 0)
    (i := 0) (i' := 0) (by simp)
    ((ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).mpr rfl)
  let i := e0.hom ≫ H'.iCycles 0
  haveI : Mono i := by dsimp only [i]; infer_instance
  apply (ModuleCat.mono_iff_injective i).mp inferInstance
  change H'.iCycles 0 (e0.hom ((truncLE'Map q (ComplexShape.embeddingUpIntLE 0)).f 0
    (intervalTruncCycle A H z hz))) = H'.iCycles 0 (e0.hom (intervalTruncCycle A H' (q.f 0 z) hz'))
  rw [truncLE'Map_f_eq_cyclesMap q (ComplexShape.embeddingUpIntLE 0) (i := 0) (i' := 0)
    ((ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).mpr rfl) (by simp)]
  simp only [ModuleCat.comp_apply]
  erw [Iso.inv_hom_id_apply, intervalTruncCycle_value]
  erw [← ModuleCat.comp_apply, cyclesMap_i]
  simp only [ModuleCat.comp_apply]
  rw [intervalTruncCycle_value]
/-- 次数−1の値を一次へ移す項同型は元の複体射で自然。 -/
theorem intervalTruncEdge_naturality {H H' : CochainComplex (ModuleCat.{u} A) ℤ}
    (q : H ⟶ H') (w : H.X (-1)) :
    (truncLE'Map q (ComplexShape.embeddingUpIntLE 0)).f 1 (intervalTruncEdge A H w) =
      intervalTruncEdge A H' (q.f (-1) w) := by
  rw [truncLE'Map_f_eq q (ComplexShape.embeddingUpIntLE 0)
    (i := 1) (i' := -1) (by rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff]; decide) (by simp)]
  dsimp only [intervalTruncEdge]
  simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
