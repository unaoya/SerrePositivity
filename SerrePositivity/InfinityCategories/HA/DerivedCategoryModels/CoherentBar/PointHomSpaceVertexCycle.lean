module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.PointHomSpaceIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CosliceFiberVertices
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreCoconeLeg
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.PinchedTopCoordinates

/-!
# 一点の余錐の脚と Hom 空間の閉零成分

## 概要
終点固定の一点の余錐の実際の脚を、同じ閉零 cycle と照合する。

## 方針
端点を固定した辺と full coefficient を使い、既存 Hom 空間同型の零次成分を読む。

## 規約
元の一単体と端点を保つ。

## 使われ方
HA 1.2.4、Kerodon 4.6.5（Tag 01KW）。指定比較余錐の余極限判定。
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
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] (x y : C)

private theorem cycleCastValHEq {a b a' b' : C} (ha : a = a') (hb : b = b')
    (h : ↥(zeroCycles (homObject R C a b)) = ↥(zeroCycles (homObject R C a' b')))
    (z : zeroCycles (homObject R C a b)) : HEq (cast h z).val z.val := by
  cases ha
  cases hb
  rfl

/-- Pinched Hom の零次の full coefficient は、同じ辺の閉零 cycle の値。 -/
theorem dgCoherentBarPinchedTop_zero (s : (PinchedHom.pinchedHom R C x y) _⦋0⦌) :
    dgCoherentBarPinchedTop R C x y s = (PinchedHom.PinchedHom.vertexCycleEquiv x y s).val := by
  apply eq_of_heq
  apply (dgCoherentBarPinchedTop_hom_heq R C x y s).trans
  symm
  change HEq (edgeCycle ((vertexEquiv (X := dgNerve R C) (Simplex.vertex x) (Simplex.vertex y)) s).toTruncated).val _
  let e := ((vertexEquiv (X := dgNerve R C) (Simplex.vertex x) (Simplex.vertex y)) s).toTruncated
  change HEq (edgeCycle e).val _
  unfold edgeCycle
  apply (cycleCastValHEq R C (edge_source_obj e) (edge_target_obj e) _ _).trans
  change HEq (s.val.edgeHom 0 1 (by decide)) _
  unfold Simplex.edgeHom
  exact SimplexData.hom_heq_of_indices_degree s.val.toSimplexData
    (by decide : ({0, 1} : Finset (Fin 2)) = Finset.univ) rfl rfl rfl

variable (D : Type v) [DGCategory R D] [Small.{u} D] {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

/-- 既存の一点 Hom 空間同型の零次成分は、元の実際の脚の同じ cycle。 -/
theorem dgCoherentBarPointHomSpaceIso_vertexCycle
    (c : (coconeMappingSpace (SSet.yonedaEquiv.symm (dgCoherentBarNativeApex R D F hMC))
      (Simplex.vertex N)) _⦋0⦌) :
    (PinchedHom.PinchedHom.vertexCycleEquiv (dgCoherentBarNormalizedModule R D F hMC) N
      ((dgCoherentBarPointHomSpaceIso R D F hMC (Simplex.vertex N)).hom.app (op ⦋0⦌) c)).val =
    (edgeCycle (cosliceFiberVertexToEdge c).toTruncated).val := by
  let M := dgCoherentBarNormalizedModule R D F hMC
  let s := (dgCoherentBarPointHomSpaceIso R D F hMC (Simplex.vertex N)).hom.app (op ⦋0⦌) c
  have ht := dgCoherentBarPointHomSpaceIso_top R D F hMC (Simplex.vertex N) c
  have hz := dgCoherentBarPinchedTop_zero R (RightModule R D) M N s
  apply eq_of_heq
  apply (heq_of_eq hz.symm).trans
  simp only [Nat.cast_zero, Int.negOnePow_zero, one_smul] at ht
  apply ht.trans
  symm
  let e := (cosliceFiberVertexToEdge c).toTruncated
  change HEq (edgeCycle e).val _
  unfold edgeCycle
  apply (cycleCastValHEq R (RightModule R D) (edge_source_obj e) (edge_target_obj e) _ _).trans
  change HEq ((cosliceFiberSimplex 0 c).edgeHom 0 1 (by decide)) _
  unfold Simplex.edgeHom
  exact SimplexData.hom_heq_of_indices_degree (cosliceFiberSimplex 0 c).toSimplexData
    (by decide : ({0, 1} : Finset (Fin 2)) = Finset.univ) rfl rfl rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
