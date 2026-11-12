module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalGraphHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalWordFunctors
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalWordComponents
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.NerveHomotopyFunctoriality

/-!
# 元の全語に整合する相対自然変換のホモトピー

概要：固定語ごとの同じ区間ホモトピーが全語の作用と可換になる。
方針：両端関手の厳密な等式と元の比較成分の回収を区間関手へ渡す。
規約：単体作用素と元の標準射の両方を保持する。
使われ方：全語の余極限上へのホモトピーの降下。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory MonoidalCategory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  {F G : LocalizerMorphism W V} (η : F.functor ⟶ G.functor)
  (hη : ∀ X, V (η.app X)) {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (X Y : C)

lemma graphHomotopy_wordAction (f : a ⟶ b) :
    (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor (W := W) (X := X) (Y := Y) f) ▷
      SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1)) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphHomotopy η hη b X Y).h =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphHomotopy η hη a X Y).h ≫
        nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor (W := V) (X := F.functor.obj X)
          (Y := G.functor.obj Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordFunctor.map f)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.hom_congr
    (Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.natTrans η hη a X Y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor (W := V) (X := F.functor.obj X)
        (Y := G.functor.obj Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordFunctor.map f)))
    (Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.natTrans η hη b X Y))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeFunctor_wordAction η X Y f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterFunctor_wordAction η X Y f)
    (fun S => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.component_wordAction η hη f S)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.hom_whiskerRight,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.hom_whiskerLeft] at h
  exact h.symm

lemma fixedWordHomotopy_wordAction (f : a ⟶ b) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f ▷
      SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1)) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedWordHomotopy η hη b X Y).h = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedWordHomotopy η hη a X Y).h := by
  change (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor (W := W) (X := X) (Y := Y) f) ▷
    SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphHomotopy η hη b X Y).h ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion V (F.functor.obj X) (G.functor.obj Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordFunctor.obj b) = _
  rw [← Category.assoc, graphHomotopy_wordAction, Category.assoc]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphHomotopy η hη a X Y).h ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram V (F.functor.obj X) (G.functor.obj Y)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordFunctor.map f) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion V (F.functor.obj X) (G.functor.obj Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordFunctor.obj b) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion_naturality]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
