module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityFiberVertices

/-!
# 恒等列の条件から元の原像 zigzag を構成

概要：包含の外が恒等列である任意の対象から、元の語の原像を構成する。
方針：元の切断の切断写像で頂点を選び、像の列の端点だけを等式で移す。
規約：元の対象は cofibrant と仮定せず、元の後ろ向きの弱同値を保持する。
使われ方：包含の像の対象の逆向きの特徴付け。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityPreimageObjects
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}
  (f : a ⟶ b) (hf : Function.Injective f.orderHom) (R : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b X Y)
  (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityOutside f R)
include hf hR

omit hR in
/-- 元の切断の fiber にある、同じ元の頂点。 -/
def vertex (i : Fin (a.length + 1)) : C := R.vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.embeddingVertex f hf i)

lemma source_eq (i : Fin a.length) :
    vertex f hf R (a.source i) = R.vertex (b.source (f.orderHom i)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.identityFiber_embeddingVertex f R hR hf _ _ (f.cut_image_source hf i)

lemma target_eq (i : Fin a.length) :
    vertex f hf R (a.target i) = R.vertex (b.target (f.orderHom i)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.identityFiber_embeddingVertex f R hR hf _ _ (f.cut_image_target hf i)

/-- 元の像の列を同じ二端点へ移した原像の列。 -/
def arrow (i : Fin a.length) : vertex f hf R (a.source i) ⟶ vertex f hf R (a.target i) :=
  eqToHom (source_eq f hf R hR i) ≫ R.arrow (f.orderHom i) ≫
    eqToHom (target_eq f hf R hR i).symm

lemma arrow_mem (i : Fin a.length) (hi : a.direction i = .backward) :
    W (arrow f hf R hR i) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.transport_mem _ _ _).2 (R.backward_mem _ ((f.direction_eq i).trans hi))

/-- 恒等列の条件から構成した、元の同じ端点を持つ原像 zigzag。 -/
def obj : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y where
  vertex := vertex f hf R
  first := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.identityFiber_embeddingVertex f R hR hf 0 0 f.cut_zero).trans R.first
  last := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.identityFiber_embeddingVertex f R hR hf _ (Fin.last b.length) f.cut_last).trans R.last
  arrow := arrow f hf R hR
  backward_mem := arrow_mem f hf R hR

lemma vertex_eq (i : Fin (a.length + 1)) (j : Fin (b.length + 1)) (h : f.cut j = i) :
    (obj f hf R hR).vertex i = R.vertex j := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.identityFiber_embeddingVertex f R hR hf i j h

/-- 原像の全列は、元の同じ像の位置の射を回収する。 -/
lemma arrow_heq (i : Fin a.length) : HEq ((obj f hf R hR).arrow i) (R.arrow (f.orderHom i)) := by
  change HEq (eqToHom _ ≫ R.arrow (f.orderHom i) ≫ eqToHom _) _
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityPreimageObjects
