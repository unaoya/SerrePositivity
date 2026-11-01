module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeNaturalGraphHomotopy
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeNaturalWordFunctors
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeNaturalWordComponents
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.NerveHomotopyFunctoriality

/-!
# 元の全語に整合する相対自然変換のホモトピー

概要：固定語ごとの同じ区間ホモトピーが全語の作用と可換になる。
方針：両端関手の厳密な等式と元の比較成分の回収を区間関手へ渡す。
規約：単体作用素と元の標準射の両方を保持する。
使われ方：全語の余極限上へのホモトピーの降下。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.RelativeNatural
open CategoryTheory MonoidalCategory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  {F G : LocalizerMorphism W V} (η : F.functor ⟶ G.functor)
  (hη : ∀ X, V (η.app X)) {a b : Word} (X Y : C)

lemma graphHomotopy_wordAction (f : a ⟶ b) :
    (nerveMap (WordAction.functor (W := W) (X := X) (Y := Y) f) ▷
      SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1)) ≫
        (graphHomotopy η hη b X Y).h =
      (graphHomotopy η hη a X Y).h ≫
        nerveMap (WordAction.functor (W := V) (X := F.functor.obj X)
          (Y := G.functor.obj Y) (wordFunctor.map f)) := by
  have h := NerveHomotopyOperations.hom_congr
    (Functor.whiskerRight (natTrans η hη a X Y)
      (WordAction.functor (W := V) (X := F.functor.obj X)
        (Y := G.functor.obj Y) (wordFunctor.map f)))
    (Functor.whiskerLeft (WordAction.functor f) (natTrans η hη b X Y))
    (beforeFunctor_wordAction η X Y f) (afterFunctor_wordAction η X Y f)
    (fun S => component_wordAction η hη f S)
  rw [NerveHomotopyOperations.hom_whiskerRight,
    NerveHomotopyOperations.hom_whiskerLeft] at h
  exact h.symm

lemma fixedWordHomotopy_wordAction (f : a ⟶ b) :
    ((graphDiagram W X Y).map f ▷
      SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1)) ≫
        (fixedWordHomotopy η hη b X Y).h = (fixedWordHomotopy η hη a X Y).h := by
  change (nerveMap (WordAction.functor (W := W) (X := X) (Y := Y) f) ▷
    SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1)) ≫
      (graphHomotopy η hη b X Y).h ≫
    graphInclusion V (F.functor.obj X) (G.functor.obj Y) (wordFunctor.obj b) = _
  rw [← Category.assoc, graphHomotopy_wordAction, Category.assoc]
  change (graphHomotopy η hη a X Y).h ≫
    (graphDiagram V (F.functor.obj X) (G.functor.obj Y)).map (wordFunctor.map f) ≫
      graphInclusion V (F.functor.obj X) (G.functor.obj Y) (wordFunctor.obj b) = _
  rw [graphInclusion_naturality]
  rfl

end SerrePositivity.EInfinity.Hammock.RelativeNatural
