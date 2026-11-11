module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectZigzagDiagram
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedWordAction
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordComposition
public import Mathlib.CategoryTheory.Whiskering

/-!
# 固定対象の全語と全相対作用素の二方向の図式

概要：相対圏の図式の全作用素と元の全語の作用を、厳密な二方向の図式へ束ねる。
方針：固定端点の相対関手と全語の作用の可換性を使い、nerve を後合成する。
規約：対象表示の等式と元の全列・全縦射を保持する。
使われ方：各自由次数の全語の余極限を取る hammock の単体的図式。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u uI vI uO
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectWordDiagram
open CategoryTheory

variable {I : Type uI} [Category.{vI} I] (D : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {O : Type uO}
  (p : (i : I) → O → (D.obj i).category)
  (hp : ∀ {i j : I} (θ : i ⟶ j) (X : O), (D.map θ).functor.obj (p i X) = p j X)

def wordMap {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) (X Y : O) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectZigzagDiagram.zigzagDiagram D p hp a X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectZigzagDiagram.zigzagDiagram D p hp b X Y where
  app i := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor (W := (D.obj i).weakEquivalences)
    (X := p i X) (Y := p i Y) f).toCatHom
  naturality _ _ θ := by
    apply Cat.Hom.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction_fixedFunctor_eq (D.map θ) (hp θ X) (hp θ Y) f

def categoryWordDiagram (X Y : O) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ I ⥤ Cat.{u, u} where
  obj w := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectZigzagDiagram.zigzagDiagram D p hp w X Y
  map f := wordMap D p hp f X Y
  map_id _ := by
    apply NatTrans.ext
    funext i
    apply Cat.Hom.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.functor_id
  map_comp f g := by
    apply NatTrans.ext
    funext i
    apply Cat.Hom.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordComposition.functor_comp f g

def graphWordDiagram (X Y : O) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ I ⥤ SSet.{u} :=
  categoryWordDiagram D p hp X Y ⋙ (CategoryTheory.Functor.whiskeringRight
    (C := I) (D := Cat.{u, u}) (E := SSet.{u})).obj nerveFunctor

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectWordDiagram
