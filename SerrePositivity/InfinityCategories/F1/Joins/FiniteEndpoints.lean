module

public import SerrePositivity.InfinityCategories.F1.Joins.FiniteLimitGeneration

/-!
概要：全有限極限・余極限から、終対象・始対象の実頂点を取り出す。
方針：空 slice の射影同型で終対象を回収し、始対象は反転で得る。
規約：実際の空図式とその普遍錐を使い、選択対象の等号を保持する。
使われ方：元の小さい圏の有限存在から、Ind の有限生成の端点を用意する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の有限余極限を、反対側の同じ有限極限へ移す。 -/
lemma hasFiniteLimits_op_of_finiteColimits {X : SSet.{u}} [HasFiniteColimits X] :
    HasFiniteLimits X.op := by
  constructor
  intro K _ p
  apply (F1B.kanHasLimit_iff_hasColimit_op p).mpr
  apply (F1B.kanHasColimit_iff_postcomp_of_isIso (SSet.opFunctor.map p)
    (SSet.opFunctorCompOpFunctorIso.app X).hom).mpr
  exact HasFiniteColimits.hasColimit (X := X) _

/-- 全有限極限を持つ単体集合は、実際の終対象の頂点を持つ。 -/
lemma exists_terminal_of_hasFiniteLimits {X : SSet.{u}} [HasFiniteLimits X] :
    ∃ t : X _⦋0⦌, IsTerminalVertex t := by
  have : IsEmpty (⊥ : X.Subcomplex).toSSet.N := ⟨fun s => s.simplex.property.elim⟩
  have : (⊥ : X.Subcomplex).toSSet.Finite := ⟨inferInstance⟩
  obtain ⟨c, hc⟩ := HasFiniteLimits.hasLimit (X := X) (⊥ : X.Subcomplex).ι
  exact ⟨c.vertex, hc.map_of_isIso (sliceOverProjection (⊥ : X.Subcomplex).ι)⟩

/-- 全有限余極限を持つ単体集合は、実際の始対象の頂点を持つ。 -/
lemma exists_initial_of_hasFiniteColimits {X : SSet.{u}} [HasFiniteColimits X] :
    ∃ t : X _⦋0⦌, IsInitialVertex t := by
  have : HasFiniteLimits X.op := hasFiniteLimits_op_of_finiteColimits
  obtain ⟨t, ht⟩ := exists_terminal_of_hasFiniteLimits (X := X.op)
  refine ⟨SSet.opObjEquiv t, (isInitialVertex_iff_isTerminalVertex_op _).mpr ?_⟩
  simpa only [Equiv.symm_apply_apply] using ht

end SerrePositivity.InfinityCategories
