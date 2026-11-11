module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordPlateauMaps
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordEmbeddingObjects

/-!
# 語の包含の像の間の縦射の元の成分の回収

概要：包含の切断の各 fiber から元の縦射の成分を回収する。
方針：切断の切断写像を一つ選び、同じ fiber 上の一致で選択からの独立性を示す。
規約：元の成分の端点だけを等式で移し、指定弱同値を保持する。
使われ方：語の包含の遷移関手の充満性。

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
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C} (f : a ⟶ b) (hf : Function.Injective f.orderHom)
  {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y}
include hf

def embeddingVertex (i : Fin (a.length + 1)) : Fin (b.length + 1) :=
  Classical.choose (f.cut_surjective hf i)

lemma cut_embeddingVertex (i : Fin (a.length + 1)) : f.cut (embeddingVertex f hf i) = i :=
  Classical.choose_spec (f.cut_surjective hf i)

/-- 元の同じ頂点に戻した、包含の像の間の縦射の成分。 -/
def embeddingApp (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f T) (i : Fin (a.length + 1)) : S.vertex i ⟶ T.vertex i :=
  eqToHom (congrArg S.vertex (cut_embeddingVertex f hf i).symm) ≫
    g.app (embeddingVertex f hf i) ≫ eqToHom (congrArg T.vertex (cut_embeddingVertex f hf i))

lemma embeddingApp_mem (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f T) (i : Fin (a.length + 1)) :
    W (embeddingApp f hf g i) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.transport_mem _ _ _).2 (g.app_mem _)

/-- 同じ切断を持つどの頂点からも、元の同じ成分を回収する。 -/
lemma embeddingApp_heq (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f T) (i : Fin (a.length + 1))
    (j : Fin (b.length + 1)) (h : f.cut j = i) : HEq (embeddingApp f hf g i) (g.app j) := by
  have he : HEq (embeddingApp f hf g i) (g.app (embeddingVertex f hf i)) := by
    unfold embeddingApp
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    rfl
  exact he.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.app_cut_eq f g _ j ((cut_embeddingVertex f hf i).trans h.symm))

omit hf in
/-- 元の端点の等式を保った二つの恒等移送の比較。 -/
lemma eqToHom_heq_of_endpoints {A B A' B' : C} (hA : A = A') (hB : B = B')
    (h : A = B) (h' : A' = B') : HEq (eqToHom h) (eqToHom h') := by
  cases hA
  cases hB
  rfl

lemma embeddingApp_first (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f T) :
    embeddingApp f hf g 0 = eqToHom (S.first.trans T.first.symm) := by
  exact eq_of_heq ((embeddingApp_heq f hf g 0 0 f.cut_zero).trans
    ((heq_of_eq g.first).trans (eqToHom_heq_of_endpoints
      (congrArg S.vertex f.cut_zero) (congrArg T.vertex f.cut_zero) _ _)))

lemma embeddingApp_last (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f T) :
    embeddingApp f hf g (Fin.last a.length) = eqToHom (S.last.trans T.last.symm) := by
  exact eq_of_heq ((embeddingApp_heq f hf g _ (Fin.last b.length) f.cut_last).trans
    ((heq_of_eq g.last).trans (eqToHom_heq_of_endpoints
      (congrArg S.vertex f.cut_last) (congrArg T.vertex f.cut_last) _ _)))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
