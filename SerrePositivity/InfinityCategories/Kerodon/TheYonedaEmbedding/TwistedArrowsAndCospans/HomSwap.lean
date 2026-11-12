module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.HomSpace
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceTwistedArrowTarget
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CylinderBoundaryEndpointConditions
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.VertexFiberTotalIso

/-!
概要：反転した底の両端固定の twisted arrow 写像空間を、元の底の逆順の両端へ移す。
方針：全空間の両端交換と底の直積の同型を比較し、固定条件と全空間の同型を fiber へ移す。
規約：充填条件を要求せず、元の全空間への包含後の射も厳密に保つ。
使われ方：元の right fibration の反転を coslice の主比較へ戻す。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- twisted arrow の反転で両端を交換する底の射。 -/
def twistedArrowBaseSwap (C : SSet.{u}) : C.op.op ⊗ C.op ⟶ C.op ⊗ C :=
  (β_ C.op.op C.op).hom ≫ (𝟙 C.op ⊗ₘ (SSet.opFunctorCompOpFunctorIso.app C).hom)

/-- 底の両端交換も厳密な同型。 -/
instance twistedArrowBaseSwap_isIso (C : SSet.{u}) : IsIso (twistedArrowBaseSwap C) := by
  unfold twistedArrowBaseSwap
  infer_instance

/-- 全空間と底の両端交換は、元の射影と厳密に可換。 -/
lemma twistedArrowOppositeSwap_projection (C : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.twistedArrowOppositeSwap C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C.op ≫ twistedArrowBaseSwap C := by
  have hfst : twistedArrowBaseSwap C ≫ fst C.op C = snd C.op.op C.op := by
    rw [twistedArrowBaseSwap, Category.assoc, tensorHom_fst, Category.comp_id, braiding_hom_fst]
  have hsnd : twistedArrowBaseSwap C ≫ snd C.op C =
      fst C.op.op C.op ≫ (SSet.opFunctorCompOpFunctorIso.app C).hom := by
    rw [twistedArrowBaseSwap, Category.assoc, tensorHom_snd, ← Category.assoc, braiding_hom_snd]
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.twistedArrowOppositeSwap_left,
      Category.assoc, hfst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_snd]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.twistedArrowOppositeSwap_right,
      Category.assoc, hsnd, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_fst]

/-- 指定した反転頂点の対は元の逆順の対に戻る。 -/
lemma twistedArrowBaseSwap_vertex {C : SSet.{u}} (x y : C _⦋0⦌) :
    (twistedArrowBaseSwap C).app (Opposite.op ⦋0⦌)
      (SSet.opObjEquiv.symm (SSet.opObjEquiv.symm y), SSet.opObjEquiv.symm x) =
        (SSet.opObjEquiv.symm x, y) := rfl

/-- 反転した底の写像空間は、元の逆順の両端の写像空間と厳密に同型。 -/
def twistedArrowHomSwapIso {C : SSet.{u}} (x y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHomSpace (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHomSpace x y := by
  let a : (C.op.op ⊗ C.op) _⦋0⦌ :=
    (SSet.opObjEquiv.symm (SSet.opObjEquiv.symm y), SSet.opObjEquiv.symm x)
  let b : (C.op ⊗ C) _⦋0⦌ := (SSet.opObjEquiv.symm x, y)
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.vertexFiberIsoOfConstraintIff (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C.op)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.twistedArrowOppositeSwap C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) a b (by
      intro L F
      have hcL : SSet.const (X := L) a ≫ twistedArrowBaseSwap C = SSet.const b := by
        rw [SSet.const_comp, twistedArrowBaseSwap_vertex]
      rw [twistedArrowOppositeSwap_projection, ← Category.assoc]
      constructor
      · intro h
        rw [h, hcL]
      · intro h
        apply (cancel_mono (twistedArrowBaseSwap C)).mp
        exact h.trans hcL.symm)
  exact e ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberTotalIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.twistedArrowOppositeSwap C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) (asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.twistedArrowOppositeSwap C)) rfl b

/-- fiber の反転同型は、元の全空間へ含めると同じ両端交換を回収する。 -/
lemma twistedArrowHomSwapIso_ι {C : SSet.{u}} (x y : C _⦋0⦌) :
    (twistedArrowHomSwapIso x y).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C)
      (SSet.opObjEquiv.symm x, y) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C.op)
      (SSet.opObjEquiv.symm (SSet.opObjEquiv.symm y), SSet.opObjEquiv.symm x) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.twistedArrowOppositeSwap C := rfl

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
