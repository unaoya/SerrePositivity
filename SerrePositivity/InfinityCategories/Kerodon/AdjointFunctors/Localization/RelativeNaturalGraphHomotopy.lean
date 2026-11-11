module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalNaturality
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitGraph
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveHomotopy

/-!
# 相対自然変換の固定語での実際の nerve ホモトピー

概要：元の比較自然変換を同じ全単体のホモトピーへ移す。
方針：既存の nerve ホモトピーと元の全語の標準射を合成する。
規約：元の両端と全縦射を保持し、モデル構造は要求しない。
使われ方：全語へ整合するホモトピーの降下。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  {F G : LocalizerMorphism W V} (η : F.functor ⟶ G.functor)
  (hη : ∀ X, V (η.app X)) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C)

def natTrans : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeFunctor η w X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterFunctor η w X Y where
  app S := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.component η hη S
  naturality _ _ f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.component_naturality η hη f

def graphHomotopy : SSet.Homotopy (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeFunctor η w X Y))
    (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterFunctor η w X Y)) := NerveHomotopy.homotopy (natTrans η hη w X Y)

def beforeMap : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph V (F.functor.obj X) (G.functor.obj Y) :=
  nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeFunctor η w X Y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion V (F.functor.obj X) (G.functor.obj Y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append w (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)))

def afterMap : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph V (F.functor.obj X) (G.functor.obj Y) :=
  nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterFunctor η w X Y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion V (F.functor.obj X) (G.functor.obj Y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append w (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)))

def fixedWordHomotopy : SSet.Homotopy (beforeMap η w X Y) (afterMap η w X Y) where
  h := (graphHomotopy η hη w X Y).h ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion V (F.functor.obj X) (G.functor.obj Y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append w (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)))
  h₀ := by rw [← Category.assoc, SSet.Homotopy.h₀]; rfl
  h₁ := by rw [← Category.assoc, SSet.Homotopy.h₁]; rfl
  rel := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
