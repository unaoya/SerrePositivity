module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ForwardPathZigzag

/-!
# forward 射列からの縦射の恒等と合成

概要：元の自然変換の恒等・合成は全頂点で同じ縦比較を与える。
方針：元の成分の定義へ戻す。
規約：両端の対象も変わってよい。
使われ方：元の全体の zigzag の図式の関手性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ForwardPath
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative] {n : ℕ}

lemma movingHom_id (F : ComposableArrows C n) (hη : ∀ i, W (𝟙 (F.obj i)))
    {X Y : C} (h0 : F.obj 0 = X) (hl : F.obj (Fin.last n) = Y) :
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.movingHom (𝟙 F) hη h0 hl h0 hl = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.zigzag F h0 hl) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ext
  intro i
  rfl

lemma movingHom_comp {F G H : ComposableArrows C n} (η : F ⟶ G) (θ : G ⟶ H)
    (hη : ∀ i, W (η.app i)) (hθ : ∀ i, W (θ.app i))
    {X Y X' Y' X'' Y'' : C} (h0 : F.obj 0 = X) (hl : F.obj (Fin.last n) = Y)
    (h0' : G.obj 0 = X') (hl' : G.obj (Fin.last n) = Y')
    (h0'' : H.obj 0 = X'') (hl'' : H.obj (Fin.last n) = Y'') :
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.movingHom η hη h0 hl h0' hl').comp (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.movingHom θ hθ h0' hl' h0'' hl'') =
      _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.movingHom (η ≫ θ) (fun i => W.comp_mem _ _ (hη i) (hθ i)) h0 hl h0'' hl'' := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ext
  intro i
  rfl

end SerrePositivity.EInfinity.Hammock.ForwardPath
