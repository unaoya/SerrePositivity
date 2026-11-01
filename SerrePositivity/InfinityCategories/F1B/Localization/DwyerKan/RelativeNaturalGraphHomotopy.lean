module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeNaturalNaturality
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ColimitGraph
public import SerrePositivity.CategoryTheory.NerveHomotopy

/-!
# 相対自然変換の固定語での実際の nerve ホモトピー

概要：元の比較自然変換を同じ全単体のホモトピーへ移す。
方針：既存の nerve ホモトピーと元の全語の標準射を合成する。
規約：元の両端と全縦射を保持し、モデル構造は要求しない。
使われ方：全語へ整合するホモトピーの降下。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.RelativeNatural
open CategoryTheory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  {F G : LocalizerMorphism W V} (η : F.functor ⟶ G.functor)
  (hη : ∀ X, V (η.app X)) (w : Word) (X Y : C)

def natTrans : beforeFunctor η w X Y ⟶ afterFunctor η w X Y where
  app S := component η hη S
  naturality _ _ f := component_naturality η hη f

def graphHomotopy : SSet.Homotopy (nerveMap (beforeFunctor η w X Y))
    (nerveMap (afterFunctor η w X Y)) := NerveHomotopy.homotopy (natTrans η hη w X Y)

def beforeMap : graph W w X Y ⟶ colimitGraph V (F.functor.obj X) (G.functor.obj Y) :=
  nerveMap (beforeFunctor η w X Y) ≫ graphInclusion V (F.functor.obj X) (G.functor.obj Y)
    (Word.append (Word.single .forward) (Word.append w (Word.single .forward)))

def afterMap : graph W w X Y ⟶ colimitGraph V (F.functor.obj X) (G.functor.obj Y) :=
  nerveMap (afterFunctor η w X Y) ≫ graphInclusion V (F.functor.obj X) (G.functor.obj Y)
    (Word.append (Word.single .forward) (Word.append w (Word.single .forward)))

def fixedWordHomotopy : SSet.Homotopy (beforeMap η w X Y) (afterMap η w X Y) where
  h := (graphHomotopy η hη w X Y).h ≫
    graphInclusion V (F.functor.obj X) (G.functor.obj Y)
      (Word.append (Word.single .forward) (Word.append w (Word.single .forward)))
  h₀ := by rw [← Category.assoc, SSet.Homotopy.h₀]; rfl
  h₁ := by rw [← Category.assoc, SSet.Homotopy.h₁]; rfl
  rel := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.EInfinity.Hammock.RelativeNatural
