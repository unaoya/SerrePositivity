module

public import SerrePositivity.InfinityCategories.F1.PointedReverseCompositionTransport
public import SerrePositivity.InfinityCategories.F1.PointedFiberTransportCoordinates
public import SerrePositivity.InfinityCategories.F1.PointSliceReverseCoordinates
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedConstantFiber

/-!
概要：反転した合成輸送の fiber 比較と、既存の左 Hom 比較の座標を照合する。
方針：両比較の元の錐の単体を取り出して、同じ反転した右 Hom の単体へ戻す。
規約：係数の反転と ULift の交換同型を明示する。
使われ方：pointed 自然性の輸送を既存の左 fiber の直接の作用へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 実際の pointed-space への全空間同型は、元の錐を底の同型で後合成する。 -/
lemma reverseKanPointCosliceIso_app_val (n : ℕ)
    (s : (sliceUnder (SSet.yonedaEquiv.symm
      (SSet.opObjEquiv.symm (coherentNerveVertex (Opposite.op pointKanObject.{u})))) _⦋n⦌)) :
    (reverseKanPointCosliceIso.hom.app (Opposite.op ⦋n⦌) s).val =
      s.val ≫ reverseKanNerveSpaceIso.hom := by
  change ((eqToHom (congrArg sliceUnder (congrArg SSet.yonedaEquiv.symm
    (reverseKanNerveSpaceIso_vertex pointKanObject)))).app (Opposite.op ⦋n⦌)
      ((pointCoslicePostIso reverseKanNerveSpaceIso _).hom.app _ s)).val = _
  rw [sliceUnder_eqToHom_app_val
    (congrArg SSet.yonedaEquiv.symm (reverseKanNerveSpaceIso_vertex pointKanObject)),
    pointCoslicePostIso_app_val]

/-- 左 pinched Hom から coslice fiber への標準同型を元の錐の射で読む。 -/
lemma pinchedLeftCosliceFiberIso_app_val {X : SSet.{u}} (x y : X _⦋0⦌) (n : ℕ)
    (s : (pinchedHomLeft x y) _⦋n⦌) :
    ((pinchedLeftCosliceFiberIso x y).hom.app (Opposite.op ⦋n⦌) s).val.val =
      (leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm (pinchedLeftSimplexVal n s) := rfl

/-- 移送した反転 Hom 比較は、宇宙と頂点を正規化すると既存の左 Hom 比較となる。 -/
lemma pointedReverseKanFiberComparison_coordinates (K : KanObject.{u}) :
    pointedReverseKanFiberComparison K =
      (HomotopyLimits.uliftOppositeIso (SimplicialCategory.sHom pointKanObject K)).inv ≫
        HomotopyLimits.coherentCosliceFiberComparison pointKanObject K ≫
        (cosliceFiberVerticesIso (spaceInfinityVertex_eq_coherent pointKanObject).symm
          (spaceInfinityVertex_eq_coherent K).symm).hom := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply Subtype.ext
  change _ = ((cosliceFiberVerticesIso
    (spaceInfinityVertex_eq_coherent pointKanObject).symm
    (spaceInfinityVertex_eq_coherent K).symm).hom.app _
      ((HomotopyLimits.coherentCosliceFiberComparison pointKanObject K).app _
        ((HomotopyLimits.uliftOppositeIso
          (SimplicialCategory.sHom pointKanObject K)).inv.app _ s))).val.val
  rw [cosliceFiberVerticesIso_app_val]
  change (reverseKanPointCosliceIso.hom.app _
    (((coherentReverseSliceFiberComparison (Opposite.op K)
      (Opposite.op pointKanObject)).app _ s).val)).val = _
  rw [reverseKanPointCosliceIso_app_val]
  change (((pointSliceReverseFiberIso (coherentNerveVertex (Opposite.op pointKanObject))
    (coherentNerveVertex (Opposite.op K))).hom.app _
      ((SSet.opFunctor.map (pinchedHomToSliceFiber _ _)).app _
        ((SSet.opFunctor.map (coherentHomComparison
          (Opposite.op K) (Opposite.op pointKanObject))).app _ s)))).val.val ≫ _ = _
  rw [pointSliceReverseFiberIso_pinched_app_val]
  change _ = ((pinchedLeftCosliceFiberIso (coherentNerveVertex pointKanObject)
    (coherentNerveVertex K)).hom.app _
      ((HomotopyLimits.coherentLeftHomComparison pointKanObject K).app _
        ((HomotopyLimits.uliftOppositeIso
          (SimplicialCategory.sHom pointKanObject K)).inv.app _ s))).val.val
  rw [pinchedLeftCosliceFiberIso_app_val, Category.assoc]
  apply congrArg (fun f ↦ (leftPointStdSimplexIso n).hom ≫ f)
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, stableReverseSimplex_yoneda, Equiv.apply_symm_apply]
  let t := ((HomotopyLimits.uliftOppositeIso
    (SimplicialCategory.sHom pointKanObject K)).inv.app (Opposite.op ⦋n⦌) s).down
  exact (HomotopyLimits.coherentLeftHomComparison_simplex pointKanObject K t).symm.trans
    (SSet.yonedaEquiv.apply_symm_apply _).symm

/-- 同じ移送した比較へ標準の一点 Hom 係数を入れると、既存の左解像比較を回収する。 -/
lemma pointedReverseKanFiberComparison_resolution (K : KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).map (pointedSpaceLeftCoefficientIso K).hom ≫
      (HomotopyLimits.uliftOppositeIso
        (SimplicialCategory.sHom pointKanObject (kanObjectOpFunctor.obj K))).hom ≫
      pointedReverseKanFiberComparison (kanObjectOpFunctor.obj K) =
        pointedSpaceLeftResolutionComparison K := by
  rw [pointedReverseKanFiberComparison_coordinates]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change coherentPointedFiberComparison K ≫ (pointedSpaceCoherentFiberIso K).hom = _
  rw [coherentPointedFiberComparison_coordinates, pointedSpaceLeftCoherentComparison_eq_resolution]

end SerrePositivity.InfinityCategories
