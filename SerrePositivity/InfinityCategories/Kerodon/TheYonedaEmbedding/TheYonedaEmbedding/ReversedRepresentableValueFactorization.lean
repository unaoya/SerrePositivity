module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ReversedRepresentableValueTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointSlicePrismReverse

/-!
概要：元の反転 Hom 値比較を、同じ反転 fiber と coslice 上の値比較に厳密に分解する。
方針：底上の同型と逆の合成を fiber の関手性で相殺する。
規約：元の値比較の選択を変更しない。使われ方：G8 の正本の値比較の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open TheSliceAndJoinConstructions MorphismSpaces IsomorphismsAndIsofibrations Equivalence
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 概要：同じ反転 Hom の値比較は、反転した元の右 fiber と coslice 上の値比較の合成。
方針：元の復元射へ戻す底上の同型と逆を fiber の誘導射で相殺する。
規約：全写像の厳密な等式。使われ方：元の表現可能値の比較を変更せず自然性を渡す。 -/
lemma representableOppositeHomValue_hom_factor {B : SSet.{u}} [Quasicategory B]
    (x z : B _⦋0⦌) :
    (representablePresheafOppositeHomValueEquivalence x z).hom =
      SSet.opFunctor.map (pinchedHomToSliceFiber x z) ≫
        (pointSliceReverseFiberIso z x).hom ≫
          (reversedRepresentableValueEquivalence z (SSet.opObjEquiv.symm x)).hom := by
  let p := SSet.opFunctor.map (sliceOverProjection (SSet.yonedaEquiv.symm z))
  let q := sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm z))
  let r := smallLeftUnstraighteningProjection (representablePresheafInfinity z)
  let e := cofinalPointSliceOverOpIso z
  let f := RepresentableUnstraighteningComparison.representableLeftUnstraighteningComparison z
  have hi : e.hom.left ≫ e.inv.left = 𝟙 _ := congrArg (fun k => k.left) e.hom_inv_id
  have hf : e.hom.left ≫ reversedRepresentableComparison z = f := by
    unfold reversedRepresentableComparison
    rw [← Category.assoc, hi, Category.id_comp]
  have hm : vertexFiberMap p q e.hom.left e.hom.w (SSet.opObjEquiv.symm x) ≫
      vertexFiberMap q r (reversedRepresentableComparison z)
        (reversedRepresentableComparison_projection z) (SSet.opObjEquiv.symm x) =
      vertexFiberMap p r f
        (RepresentableUnstraighteningComparison.representableLeftUnstraighteningComparison_projection z)
          (SSet.opObjEquiv.symm x) := by
    rw [vertexFiberMap_comp]
    apply vertexFiber_hom_ext r (SSet.opObjEquiv.symm x)
    rw [vertexFiberMap_ι, vertexFiberMap_ι, hf]
  simp only [representablePresheafOppositeHomValueEquivalence,
    reversedRepresentableValueEquivalence, pointSliceReverseFiberIso, QCatEquivalence.trans,
    qCatEquivalenceOfIso, IsQCatEquivalence.choose, Iso.trans_hom, vertexFiberTotalIso,
    Functor.mapIso_hom, Category.assoc]
  have h₀ : (pinchedHomSliceFiberIso x z).hom = pinchedHomToSliceFiber x z := rfl
  simp only [h₀]
  have hh := congrArg (fun k => SSet.opFunctor.map (pinchedHomToSliceFiber x z) ≫
    (SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.oppositeVertexFiberIso
      (sliceOverProjection (SSet.yonedaEquiv.symm z)) x).hom ≫ k ≫
      (smallLeftUnstraighteningFiberValueEquivalence (representablePresheafInfinity z)
        (SSet.opObjEquiv.symm x)).hom) hm
  simpa only [p, q, r, e, f, Over.forget_map, Over.mk_hom, Category.assoc] using hh.symm

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
