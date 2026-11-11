module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianStrictTransport

/-!
概要：薄い通常圏の undercategory の反変な nerve 射は単射。
方針：元の射列の各対象を標的対象から戻し、薄さで構造射と射の一致を確認する。
規約：大域 instance を追加せず、元の undercategory 射の単射性を明示する。
使われ方：有限単体上の strict transport の制限の相対持ち上げ性。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 薄い底の元の undercategory の反変な nerve 射は、全次数で単射。 -/
lemma kanCocartesianUnderMap_mono_of_thin
    {C : Type u} [Category.{u} C] [Quiver.IsThin C] {c d : C} (f : c ⟶ d) :
    Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro σ τ h
  change σ ⋙ Under.map f = τ ⋙ Under.map f at h
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
  · have hr : (σ.obj i).right = (τ.obj i).right :=
      congrArg (fun H : ComposableArrows (Under c) n.unop.len ↦ (H.obj i).right) h
    exact StructuredArrow.obj_ext (σ.obj i) (τ.obj i) hr (Subsingleton.elim _ _)
  · intro i j g
    apply StructuredArrow.ext
    exact Subsingleton.elim _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
