module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.RightFibrationRetracts
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletenessOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalOppositeFibration

/-!
概要：指定した元の頂点の底の retract を、左 fibration の全体へ持ち上げる。
方針：同じ元の反転射の右 fibration の持ち上げを、反転の頂点同型で戻す。
規約：元の分裂点と指定した底の非分裂点を保持する。
使われ方：固定した始点から出る辺の全関手圏内の retract。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 指定した元の頂点を持つ底の retract は、左 fibration の全体へ持ち上がる。 -/
lemma leftFibration_retract_lift {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (p : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction (p.app (Opposite.op ⦋0⦌) x) y) :
    ∃ z : X _⦋0⦌, p.app (Opposite.op ⦋0⦌) z = y ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf x z := by
  have hr := (show _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf (p.app (Opposite.op ⦋0⦌) x) y from ⟨r⟩).op
  have hro : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf
      ((SSet.opFunctor.map p).app (Opposite.op ⦋0⦌) (SSet.opObjEquiv.symm x))
      (SSet.opObjEquiv.symm y) := by
    simpa only [SSet.opFunctor_map, Equiv.apply_symm_apply] using hr
  obtain ⟨z, hz, hxz⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.rightFibration_retract_lift (SSet.opFunctor.map p)
    (SSet.opObjEquiv.symm x) (SSet.opObjEquiv.symm y) hro.some
  refine ⟨SSet.opObjEquiv z, ?_, ?_⟩
  · have h := congrArg (SSet.opObjEquiv (X := Y)) hz
    simpa only [SSet.opFunctor_map, Equiv.apply_symm_apply] using h
  · have h := hxz.op.map (SSet.opFunctorCompOpFunctorIso.app X).hom
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf
      (SSet.opObjEquiv (SSet.opObjEquiv (SSet.opObjEquiv.symm (SSet.opObjEquiv.symm x))))
      (SSet.opObjEquiv (SSet.opObjEquiv (SSet.opObjEquiv.symm z))) at h
    simpa only [Equiv.apply_symm_apply] using h

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
