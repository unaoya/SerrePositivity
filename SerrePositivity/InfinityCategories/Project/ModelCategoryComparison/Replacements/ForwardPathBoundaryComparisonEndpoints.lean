module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ForwardPathBoundaryComparisons

/-!
# 動く境界ブロックの比較の端点成分

概要：全ブロックの比較から、元の内側と外側の縦射を回収する。
方針：貼り合わせの左右の成分回収を、元の自然変換と一列の正方形へ適用。
規約：内外の端点の射はいずれも動いてよい。
使われ方：元の中央 backward 列の全縦射の貼り合わせ。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] {n : ℕ}

lemma leftBoundaryComparison_first {F G : ComposableArrows C n} (η : F ⟶ G)
    (hη : ∀ i, weakEquivalences C (η.app i)) {X X' : C}
    (e : F.obj 0 ⟶ X) (e' : G.obj 0 ⟶ X')
    (he : weakEquivalences C e) (he' : weakEquivalences C e')
    (x : X ⟶ X') (hx : weakEquivalences C x) (h : e ≫ x = η.app 0 ≫ e') :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryComparison η hη e e' he he' x hx h).app 0) x := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map]
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq _
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.movingHom η hη rfl rfl rfl rfl) 0)
  rfl

lemma leftBoundaryComparison_last {F G : ComposableArrows C n} (η : F ⟶ G)
    (hη : ∀ i, weakEquivalences C (η.app i)) {X X' : C}
    (e : F.obj 0 ⟶ X) (e' : G.obj 0 ⟶ X')
    (he : weakEquivalences C e) (he' : weakEquivalences C e')
    (x : X ⟶ X') (hx : weakEquivalences C x) (h : e ≫ x = η.app 0 ≫ e') :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryComparison η hη e e' he he' x hx h).app
      (Fin.last (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord n).length)) (η.app (Fin.last n)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map]
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_right_heq _
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.movingHom η hη rfl rfl rfl rfl) HEq.rfl (Fin.last n))
  rfl

lemma rightBoundaryComparison_first {F G : ComposableArrows C n} (η : F ⟶ G)
    (hη : ∀ i, weakEquivalences C (η.app i)) {Y Y' : C}
    (e : Y ⟶ F.obj (Fin.last n)) (e' : Y' ⟶ G.obj (Fin.last n))
    (he : weakEquivalences C e) (he' : weakEquivalences C e')
    (y : Y ⟶ Y') (hy : weakEquivalences C y) (h : e ≫ η.app (Fin.last n) = y ≫ e') :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryComparison η hη e e' he he' y hy h).app 0) (η.app 0) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map]
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.movingHom η hη rfl rfl rfl rfl) _ 0)
  rfl

lemma rightBoundaryComparison_last {F G : ComposableArrows C n} (η : F ⟶ G)
    (hη : ∀ i, weakEquivalences C (η.app i)) {Y Y' : C}
    (e : Y ⟶ F.obj (Fin.last n)) (e' : Y' ⟶ G.obj (Fin.last n))
    (he : weakEquivalences C e) (he' : weakEquivalences C e')
    (y : Y ⟶ Y') (hy : weakEquivalences C y) (h : e ≫ η.app (Fin.last n) = y ≫ e') :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryComparison η hη e e' he he' y hy h).app
      (Fin.last (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord n).length)) y := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map]
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_right_heq (b := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.movingHom η hη rfl rfl rfl rfl) _ HEq.rfl (Fin.last 1))
  rfl

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
