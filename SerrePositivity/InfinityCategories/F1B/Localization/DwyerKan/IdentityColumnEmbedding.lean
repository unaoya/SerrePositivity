module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.IdentityColumn
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordEmbeddingMapComponents

/-!
# 包含の像の列から元の恒等列を回収

概要：元の語の包含は、像の位置で元の恒等列の条件を保存し反映する。
方針：包含の前後の切断・元の列・等式による恒等移送を照合する。
規約：元の対象と射の等式を保持する。
使われ方：一つの恒等列を削除した後にも他の恒等列が残ることの証明。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {a b : Word} {X Y : C} (f : a ⟶ b) (hf : Function.Injective f.orderHom)
  (S : Zigzag W a X Y) (i : Fin a.length)
include hf

lemma identityColumn_obj_image_iff :
    IdentityColumn (WordAction.obj f S) (f.orderHom i) ↔ IdentityColumn S i := by
  have hs := congrArg S.vertex (f.cut_image_source hf i)
  have ht := congrArg S.vertex (f.cut_image_target hf i)
  have hp := WordAction.vertex_image_castSucc f hf S i
  have hq := WordAction.vertex_image_succ f hf S i
  constructor
  · intro h
    refine ⟨hp.symm.trans (h.vertex_eq.trans hq), ?_⟩
    exact eq_of_heq ((WordAction.arrow_image_heq f hf S i).symm.trans
      ((heq_of_eq h.arrow_eq).trans (WordAction.eqToHom_heq_of_endpoints hs ht _ _)))
  · intro h
    refine ⟨hp.trans (h.vertex_eq.trans hq.symm), ?_⟩
    exact eq_of_heq ((WordAction.arrow_image_heq f hf S i).trans
      ((heq_of_eq h.arrow_eq).trans (WordAction.eqToHom_heq_of_endpoints hs.symm ht.symm _ _)))

end SerrePositivity.EInfinity.Hammock
