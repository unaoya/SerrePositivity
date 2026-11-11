module

public import SerrePositivity.EInfinity.Hammock.SingleZigzagGraphValue
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SingleZigzagRelativeValue
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagNativeRelative
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectZigzagDiagram
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeMarkedCategory
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeUnderlyingCategory
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom

/-!
# 元の単一列の graph から固定 Hom 図式への評価

概要：全相対作用素の元の一列の評価を自然変換に束ねる。
方針：前向きは元の Hom、後向きは実際の指定部分圏の Hom を使う。
規約：元の端点移送と全縦射を保持する。
使われ方：DK5.7の対角比較の基底。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.EInfinity.Hammock.FixedObjectDiagram
open CategoryTheory
variable {I : Type v} [Category I] (D : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {O : Type w}
  (p : (i : I) → O → (D.obj i).category)
  (hp : ∀ {i j : I} (θ : i ⟶ j) (X : O), (D.map θ).functor.obj (p i X) = p j X)

def markedObject (i : I) (X : O) : WideSubcategory (D.obj i).weakEquivalences := ⟨p i X⟩
include hp in
lemma markedObject_naturality {i j : I} (θ : i ⟶ j) (X : O) :
    ((D ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryFunctor).map θ).toFunctor.obj (markedObject D p i X) =
      markedObject D p j X := congrArg (fun Z => (⟨Z⟩ : WideSubcategory
        (D.obj j).weakEquivalences)) (hp θ X)

def forwardHomDiagram (X Y : O) : I ⥤ Type u :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.functor (D ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.underlyingCategoryFunctor) p hp X Y

def backwardHomDiagram (X Y : O) : I ⥤ Type u :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.functor (D ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryFunctor) (markedObject D p)
    (markedObject_naturality D p hp) Y X

def singleForwardEvaluation (X Y : O) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectZigzagDiagram.graphDiagram D p hp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) X Y ⟶
    forwardHomDiagram D p hp X Y ⋙ Functor.const SimplexCategoryᵒᵖ where
  app i := ForwardZigzag.graphValue
  naturality i j θ := by
    ext n σ
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.value_relative (D.map θ) (hp θ X) (hp θ Y) (σ.obj 0)

def singleBackwardEvaluation (X Y : O) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectZigzagDiagram.graphDiagram D p hp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) X Y ⟶
    backwardHomDiagram D p hp X Y ⋙ Functor.const SimplexCategoryᵒᵖ where
  app i := BackwardZigzag.graphValue
  naturality i j θ := by
    ext n σ
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.nativeValue_relative (D.map θ) (hp θ X) (hp θ Y) (σ.obj 0)
end SerrePositivity.EInfinity.Hammock.FixedObjectDiagram
