module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.ClosedMapCoconeCoordinates
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.NativeVertexModuleMaps
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.EdgeHomotopy

/-!
# 同じ指定余錐の実際の脚

## 概要
join余錐の実際の辺の閉零係数を、native頂点列と指定閉射の合成へ照合する。
## 方針
零単体の余錐座標と端点のcastを保持し、同じfull coefficientを読む。
## 規約
脚のホモロジーだけでなく、閉零係数そのものを比較する。
## 使われ方
HA 1.2.4、HTT 4.2.4.1。指定実現余錐の標準脚。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Opposite SSet SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open StrictComparison
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}} (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (N : RightModule R D)
  (f : ForgetEnrichment.of (Complex R) (dgCoherentBarNormalizedModuleUnconditional R D F) ⟶
    ForgetEnrichment.of (Complex R) N)

/-- 指定した余錐の実際の脚は、同じ閉射とnative頂点列の合成を表す。 -/
theorem dgCoherentBarClosedMapCocone_leg_cycle (s : I _⦋0⦌) :
    HEq (edgeCycle ((dgCoherentBarClosedMapCocone R D F N f).leg
      (SSet.yonedaEquiv.symm (ULift.up s)))).val
      (((closedHomEquiv R (RightModule R D) _ _)
        (dgBarNativeVertexModuleMap R D F s ≫ f)).val) := by
  let c := dgCoherentBarClosedMapCoconePoint R D F N f
  let t : dgCoherentBarNormalizedIndex I := ⟨⟨0, s⟩, by simp [SSet.nondegenerate_zero]⟩
  have h := dgCoherentBarCoconeFamilyHom_nondegenerate R D F
    (dgCoherentBarMaurerCartan_unconditional R D F) (Simplex.vertex N) c t
  rw [dgCoherentBarClosedMapCoconePoint_familyHom] at h
  have hp := moduleHomCycle_postcompose R D (dgBarNativeVertexModuleMap R D F s) f
  rw [dgBarNativeVertexModuleMap_cycle, dgStrictPostcompose_eq_compose] at hp
  have hc := h.symm.trans hp
  apply (SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeCycle_val_heq _).trans
  apply HEq.trans ?_ (heq_of_eq hc)
  unfold dgCoherentBarCoconeFamilyColumn
  symm
  apply (gradedHomTransport_heq _ _ _ _).trans
  change HEq ((dgCoherentBarCoconeFamilySimplex R D F (Simplex.vertex N) c s).hom
    Finset.univ 0 1 0 (by decide) (by decide) (by decide) (by decide))
      ((dgCoherentBarCoconeFamilySimplex R D F (Simplex.vertex N) c s).edgeCycle 0 1 (by decide)).val
  unfold Simplex.edgeCycle Simplex.edgeHom
  dsimp only []
  exact SimplexData.hom_heq_of_indices_degree
    (dgCoherentBarCoconeFamilySimplex R D F (Simplex.vertex N) c s).toSimplexData
    (by decide : (Finset.univ : Finset (Fin 2)) = {0, 1}) rfl rfl rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
