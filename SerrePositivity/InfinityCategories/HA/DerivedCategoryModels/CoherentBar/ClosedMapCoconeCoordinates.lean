module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.ClosedMapCocone
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.PointHomSpaceVertexCycle
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLinearData
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeHomSpaceComparison

/-!
# 指定閉射から戻した余錐の同じ線形座標

## 概要
終点固定の余錐空間同型の零次成分を、元の閉射の同じcycleへ照合する。
## 方針
零次のfull coefficientを回収し、単点の自己写像の一意性を使う。
## 規約
余錐の終点と全高次成分を変えない。
## 使われ方
HA 1.2.4。計算した標準脚と実際のnative余錐の接続。
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
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}} (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

/-- 零次の余錐Hom比較は、同じ余錐族の閉零係数を返す。 -/
theorem dgCoherentBarCoconeHomSpaceComparison_zero
    (c : (coconeMappingSpace F (Simplex.vertex N)) _⦋0⦌) :
    dgCoherentBarPinchedTop R (RightModule R D) (dgCoherentBarNormalizedModule R D F hMC) N
      ((dgCoherentBarCoconeHomSpaceComparison R D F hMC (Simplex.vertex N)).app (op ⦋0⦌) c) =
      dgCoherentBarCoconeFamilyHom R D F hMC (Simplex.vertex N) c := by
  unfold dgCoherentBarPinchedTop
  rw [dgCoherentBarCoconeHomSpaceComparison_linear]
  change dgCoherentBarCoconeSubsetHom R D F hMC (Simplex.vertex N) c Finset.univ 0 Finset.univ_nonempty (by simp) = _
  have h := dgCoherentBarCoconeSubsetHom_heq R D F hMC (Simplex.vertex N) c
    Finset.univ 0 Finset.univ_nonempty (by simp) 0 (by simp)
  simp only [Nat.cast_zero, Int.negOnePow_zero, one_smul] at h
  apply eq_of_heq
  apply h.trans
  unfold dgCoherentBarCoconeSubsetParameterHom
  have hr : SimplexCategory.mkHom
      ((Finset.univ : Finset (Fin 1)).orderEmbOfFin (by simp)).toOrderHom = 𝟙 ⦋0⦌ :=
    Subsingleton.elim _ _
  rw [hr]
  have hc : (coconeMappingSpace F (Simplex.vertex N)).map (𝟙 ⦋0⦌).op c = c := by
    exact ConcreteCategory.congr_hom ((coconeMappingSpace F (Simplex.vertex N)).map_id (op ⦋0⦌)) c
  rw [hc]

/-- 指定余錐族の零次係数は、最初の同じ閉射のcycleである。 -/
theorem dgCoherentBarClosedMapCoconePoint_familyHom
    (f : ForgetEnrichment.of (Complex R) (dgCoherentBarNormalizedModuleUnconditional R D F) ⟶
      ForgetEnrichment.of (Complex R) N) :
    dgCoherentBarCoconeFamilyHom R D F (dgCoherentBarMaurerCartan_unconditional R D F)
      (Simplex.vertex N) (dgCoherentBarClosedMapCoconePoint R D F N f) =
        ((closedHomEquiv R (RightModule R D) _ _) f).val := by
  rw [← dgCoherentBarCoconeHomSpaceComparison_zero]
  rw [dgCoherentBarPinchedTop_zero]
  exact congrArg Subtype.val (dgCoherentBarClosedMapCoconePoint_cycle R D F N f)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
