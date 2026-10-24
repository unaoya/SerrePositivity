module

public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaInfinityFullyFaithful
public import SerrePositivity.InfinityCategories.F2.Compact.RepresentableRetractions
public import SerrePositivity.InfinityCategories.F2.Idempotent.CompleteImageRetracts
public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletenessUniverse
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor

/-!
概要：冪等完備な圏の全共変表現可能関手の retract は再び元の対象で余表現可能。
方針：反対圏の Yoneda と二重反転による前合成の充満忠実性を使う。
規約：元の全関手圏の retract を要求し、点ごとの分裂に弱めない。
使われ方：解関手の全自然な retract から元の余表現対象を回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：元の対象から全共変表現可能関手を取る反変関手は充満忠実。
方針：反対圏の元の Yoneda を二重反転の厳密な同型で前合成する。
規約：元の共変 Hom 関手を使う。
使われ方：その全自然な retract の元の圏での分裂。 -/
lemma covariantRepresentableDiagram_isFullyFaithful (C : SSet.{u}) [Quasicategory C] :
    IsFullyFaithful (Compact.covariantRepresentableDiagram C) := by
  let e := (SSet.uliftFunctor.{u + 1, u}).mapIso
    (SSet.opFunctorCompOpFunctorIso.app C).symm
  have hp := (isPrecompositionEquivalence_of_iso e) SpaceInfinity.{u}
  exact (yonedaInfinityMap_isFullyFaithful C.op).comp hp.isFullyFaithful

/-- 概要：全共変表現可能関手の元の全自然な retract は元の対象で余表現可能。
方針：反対圏の冪等完備性と全共変 Yoneda の本質像の retract 閉性を使う。
規約：指定した元の関手 H と全自然な比較を保持する。
使われ方：accessible な小極限保存関手の余表現可能性の最後の分裂。 -/
lemma covariantRepresentable_retract_corepresentable {C : SSet.{u}} [Quasicategory C]
    (hC : Idempotent.IsIdempotentComplete C)
    (H : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ SpaceInfinity.{u})
    (y : C _⦋0⦌)
    (r : Idempotent.VertexRetraction (functorVertex H)
      (functorVertex (covariantRepresentableInfinity y))) :
    ∃ x : C _⦋0⦌, Nonempty (FunctorIso (covariantRepresentableInfinity x) H) := by
  have hr : Idempotent.VertexRetraction (functorVertex H)
      ((Compact.covariantRepresentableDiagram C).app (Opposite.op ⦋0⦌)
        (ULift.up (SSet.opObjEquiv.symm y))) := by
    rw [Compact.covariantRepresentableDiagram_vertex]
    exact r
  obtain ⟨⟨z⟩, ⟨e⟩⟩ := hC.op.ulift.retract_iso_in_image
    (Compact.covariantRepresentableDiagram C) (covariantRepresentableDiagram_isFullyFaithful C)
    (ULift.up (SSet.opObjEquiv.symm y)) (functorVertex H) hr
  have hv := Compact.covariantRepresentableDiagram_vertex (SSet.opObjEquiv z)
  simp only [Equiv.symm_apply_apply] at hv
  rw [hv] at e
  exact ⟨SSet.opObjEquiv z, ⟨e.symm⟩⟩

end SerrePositivity.InfinityCategories.F2.Presentable
