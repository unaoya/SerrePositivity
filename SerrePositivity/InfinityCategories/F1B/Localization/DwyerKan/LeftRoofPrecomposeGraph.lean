module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.LeftRoofPrecomposeUpperOriginal
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.LeftRoofPrecomposeLowerOriginal
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.PointActions
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ColimitArrowMap
public import Mathlib.CategoryTheory.Category.ULift

/-!
# 元の要素図式の四列比較を全 graph と余極限へ移す

概要：元の Hom 宇宙の異なる要素図式の全射列を同じ graph へ送る。
方針：全語の標準射の自然性と元の連結の式を使う。
規約：元の全単体・全作用素・元の前合成を保持する。
使われ方：始域比較のホモトピーを元の余極限へ渡す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Hammock.LeftRoof.Precompose
open CategoryTheory
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {I : Type v} [Category.{0} I] {B E X' X Y : C} {w : Word}

def diagramGraphMap (F : I ⥤ Zigzag W w B E) : nerve (ULiftHom.{max u v} I) ⟶ graph W w B E where
  app _ := ↾fun σ => σ ⋙ ULiftHom.down.{0, v, max u v} ⋙ F
  naturality _ _ _ := rfl

def diagramColimitMap (F : I ⥤ Zigzag W w B E) :
    nerve (ULiftHom.{max u v} I) ⟶ colimitGraph W B E :=
  diagramGraphMap W F ≫ graphInclusion W B E w

lemma diagramColimitMap_wordAction (F : I ⥤ Zigzag W w B E) {w' : Word} (f : w ⟶ w') :
    diagramColimitMap W (F ⋙ WordAction.functor f) = diagramColimitMap W F := by
  have h : diagramGraphMap W (F ⋙ WordAction.functor f) =
      diagramGraphMap W F ≫ (graphDiagram W B E).map f := rfl
  unfold diagramColimitMap
  rw [h, Category.assoc, graphInclusion_naturality]

lemma diagramColimitMap_precompose (F : I ⥤ Zigzag W LeftRoof.word X Y) (f : X' ⟶ X) :
    diagramColimitMap W
        (((Functor.const I).obj (ForwardZigzag.obj (W := W) f)).prod' F ⋙ ZigzagAppend.functor) =
      diagramColimitMap W F ≫ precomposePointMap (arrowMap W f) Y := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro σ
  let Γ := σ ⋙ ULiftHom.down.{0, v, max u v} ⋙ F
  change (graphInclusion W X' Y preWord).app n
      ((arrowSimplex W f n).prod' Γ ⋙ ZigzagAppend.functor) =
    composePoint W X' X Y (arrowPoint W f n)
      ((graphInclusion W X Y LeftRoof.word).app n Γ)
  exact (composePoint_inclusions W X' X Y (Word.single .forward) LeftRoof.word
    (arrowSimplex W f n) Γ).symm

end SerrePositivity.EInfinity.Hammock.LeftRoof.Precompose
