module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityPreimageObjects
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GraphEmbeddingRange

/-!
# 恒等列の条件による元の対象と全単体の像の特徴付け

概要：包含の外が恒等列なら、構成した原像は元の対象を厳密に回収する。
方針：像の列と恒等列を別々に回収し、対象と全射列の外延性を使う。
規約：元の各列・各頂点の等式を保持し、同型だけで代用しない。
使われ方：二つの語の包含の graph の像の交わり。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) (hf : Function.Injective f.orderHom) {X Y : C}
include hf

/-- 恒等列の条件から構成した元の原像は、同じ元の対象を厳密に回収する。 -/
lemma IdentityPreimage.obj_image (R : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b X Y) (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityOutside f R) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityPreimageObjects.obj f hf R hR) = R := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext
  · intro j
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityPreimageObjects.vertex_eq f hf R hR (f.cut j) j rfl
  · intro j
    by_cases hj : ∃ i, f.orderHom i = j
    · obtain ⟨i, rfl⟩ := hj
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.arrow_image_heq f hf _ i).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityPreimageObjects.arrow_heq f hf R hR i)
    · have hno : ∀ i, f.orderHom i ≠ j := fun i hi => hj ⟨i, hi⟩
      have hcut := f.cut_empty_fiber j hno
      have he := f.cut_source_target_of_eq j hcut
      change HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.column f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityPreimageObjects.obj f hf R hR) j) (R.arrow j)
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.column_eqToHom_of_cut_eq f _ j hcut he, (hR j hno).arrow_eq]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.eqToHom_heq_of_endpoints
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityPreimageObjects.vertex_eq f hf R hR _ (b.source j) rfl)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityPreimageObjects.vertex_eq f hf R hR _ (b.target j) rfl) _ _

lemma WordAction.obj_range_iff (R : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b X Y) :
    R ∈ Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityOutside f R := by
  constructor
  · rintro ⟨S, rfl⟩
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.identityOutside_obj f S
  · intro hR
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityPreimageObjects.obj f hf R hR, IdentityPreimage.obj_image f hf R hR⟩

/-- 全単体の像は、元の全行の像の外の恒等列で厳密に特徴付けられる。 -/
lemma graphDiagram_map_range_iff_identityOutside (n : SimplexCategoryᵒᵖ)
    (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W b X Y).obj n) :
    τ ∈ Set.range (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f).app n) ↔
      ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityOutside f (τ.obj j) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphDiagram_map_range_iff W f hf X Y n τ]
  exact forall_congr' (fun j => WordAction.obj_range_iff f hf (τ.obj j))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
