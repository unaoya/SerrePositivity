module

public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletionOpposite
public import SerrePositivity.InfinityCategories.F1.FullyFaithfulPostcomposition

/-!
概要：元の任意の冪等完備化と充満忠実性は、inner 仮定なしで反転できる。
方針：元の頂点像への同値と全部分圏の包含へ因子化し、保存済みの反転を合成する。
規約：元の全射そのものの反転を結論する。
使われ方：零対象の保存の始対象側への双対化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の充満忠実な射は、inner 仮定なしで反転しても充満忠実。 -/
lemma isFullyFaithful_op_of_fullyFaithful {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) (hf : IsFullyFaithful f) :
    IsFullyFaithful (SSet.opFunctor.map f) := by
  let P := fun y ↦ ∃ x, f.app (Opposite.op ⦋0⦌) x = y
  let e := fullSubcomplexLift P f (fun x ↦ ⟨x, rfl⟩)
  let i := (fullSubcomplexOnVertices Y P).ι
  have he : IsQCatEquivalence e := fullSubcomplexVertexImageLift_isQCatEquivalence f hf
  have hi : IsFullyFaithful i := isFullyFaithful_fullSubcomplexOnVertices_ι Y P
  have : InnerFibration i := inferInstanceAs (InnerFibration (fullSubcomplexOnVertices Y P).ι)
  have h := (F1B.kanIsQCatEquivalence_op he).isFullyFaithful.comp
    (F1B.kanIsFullyFaithful_op i hi)
  have hfac : e ≫ i = f := fullSubcomplexLift_ι _ _ _
  have ho : SSet.opFunctor.map e ≫ SSet.opFunctor.map i = SSet.opFunctor.map f :=
    (SSet.opFunctor.map_comp e i).symm.trans (congrArg SSet.opFunctor.map hfac)
  exact ho ▸ h

/-- 元の任意の冪等完備化は、単射性・inner 仮定なしで同じ元の反転射へ移る。 -/
lemma IsIdempotentCompletion.op_general {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : IsIdempotentCompletion f) :
    IsIdempotentCompletion (SSet.opFunctor.map f) := by
  refine ⟨hf.1.op, isFullyFaithful_op_of_fullyFaithful f hf.2.1, ?_⟩
  intro d
  obtain ⟨c, hc⟩ := hf.2.2 (SSet.opObjEquiv d)
  refine ⟨SSet.opObjEquiv.symm c, ?_⟩
  rw [SSet.opFunctor_map, Equiv.apply_symm_apply]
  simpa only [Equiv.symm_apply_apply] using hc.op

end SerrePositivity.InfinityCategories.F2.Idempotent
