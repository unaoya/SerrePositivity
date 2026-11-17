module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolutionFunctoriality
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ComonadSimplicialResolution

/-!
# Comonad の全単体的解像の係数関手

概要：Dwyer–Kan の解像に係数の射を全単体作用素と両立して送る。
方針：表示単体圏の生成射への自然性を帰納し、同じ通常の単体圏へ移す。
規約：元の解像と augmentation を保持する。
使われ方：相対関手を単体的局所化の間の関手へ送る。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution

open _root_.CategoryTheory _root_.Opposite
open _root_.SerrePositivity.HomotopyFunctionComplex

variable {C : Type u} [Category.{v} C] (G : Comonad C)

/-- 概要：表示単体圏の全作用素に対する冪の係数自然性（Dwyer–Kan）。
方針：面・退化の自然性を生成射に沿う帰納で合成する。
規約：元の反対図式を使う。
使われ方：同じ全解像の間の自然変換の構成。 -/
lemma oppositeMap_naturality {X Y : C} (f : X ⟶ Y)
    {n m : SimplexCategoryGenRel} (θ : n ⟶ m) :
    (ComonadResolutionPresentation.oppositeDiagram G Y).map θ ≫
        (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f (m.len + 1)).op =
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f (n.len + 1)).op ≫
        (ComonadResolutionPresentation.oppositeDiagram G X).map θ := by
  let P : MorphismProperty SimplexCategoryGenRel := fun {n m} θ =>
    (ComonadResolutionPresentation.oppositeDiagram G Y).map θ ≫
        (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f (m.len + 1)).op =
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f (n.len + 1)).op ≫
        (ComonadResolutionPresentation.oppositeDiagram G X).map θ
  refine SimplexCategoryGenRel.hom_induction P ?_ ?_ ?_ θ
  · intro n
    change (ComonadResolutionPresentation.oppositeDiagram G Y).map
        (𝟙 (SimplexCategoryGenRel.mk n)) ≫ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f (n + 1)).op =
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f (n + 1)).op ≫
        (ComonadResolutionPresentation.oppositeDiagram G X).map (𝟙 (SimplexCategoryGenRel.mk n))
    exact (congrArg (fun g => g ≫ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f (n + 1)).op)
      ((ComonadResolutionPresentation.oppositeDiagram G Y).map_id
        (SimplexCategoryGenRel.mk n))).trans
      ((Category.id_comp _).trans ((Category.comp_id _).symm.trans
        (congrArg (fun g => (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f (n + 1)).op ≫ g)
          ((ComonadResolutionPresentation.oppositeDiagram G X).map_id
            (SimplexCategoryGenRel.mk n))).symm))
  · intro n m θ i ih
    have hd : P (SimplexCategoryGenRel.δ i) := by
      change (ComonadResolutionPresentation.oppositeDiagram G Y).map
          (SimplexCategoryGenRel.δ i) ≫ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f (m + 2)).op =
        (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f (m + 1)).op ≫
          (ComonadResolutionPresentation.oppositeDiagram G X).map
            (SimplexCategoryGenRel.δ i)
      simpa only [ComonadResolutionPresentation.oppositeDiagram_face, op_comp] using
        congrArg Quiver.Hom.op (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.face_naturality G f (m + 1) i)
    change _ ≫ _ = _ ≫ _ at ih hd ⊢
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      Category.assoc, hd, ← Category.assoc, ih,
      Category.assoc]
  · intro n m θ i ih
    have hd : P (SimplexCategoryGenRel.σ i) := by
      change (ComonadResolutionPresentation.oppositeDiagram G Y).map
          (SimplexCategoryGenRel.σ i) ≫ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f (m + 1)).op =
        (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f (m + 2)).op ≫
          (ComonadResolutionPresentation.oppositeDiagram G X).map
            (SimplexCategoryGenRel.σ i)
      simpa only [ComonadResolutionPresentation.oppositeDiagram_degeneracy, op_comp] using
        congrArg Quiver.Hom.op (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.degeneracy_naturality G f m i)
    change _ ≫ _ = _ ≫ _ at ih hd ⊢
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      Category.assoc, hd, ← Category.assoc, ih,
      Category.assoc]

/-- 概要：表示単体圏上の反対解像の係数射（Dwyer–Kan）。
方針：元の冪の射の反対射と全作用素への自然性を束ねる。
規約：反対化により係数の向きが反転する。
使われ方：元の圏に戻した解像の係数関手。 -/
def oppositeMap {X Y : C} (f : X ⟶ Y) :
    ComonadResolutionPresentation.oppositeDiagram G Y ⟶
      ComonadResolutionPresentation.oppositeDiagram G X where
  app n := (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f (n.len + 1)).op
  naturality _ _ θ := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.oppositeMap_naturality G f θ

/-- 概要：表示単体圏上の元の解像の係数射（Dwyer–Kan）。
方針：同じ反対解像の自然変換を leftOp で戻す。
規約：元の係数射の向きを保持する。
使われ方：通常の単体圏への同じ係数関手の移送。 -/
def presentationMap {X Y : C} (f : X ⟶ Y) :
    ComonadResolutionPresentation.diagram G X ⟶ ComonadResolutionPresentation.diagram G Y :=
  NatTrans.leftOp (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.oppositeMap G f)

/-- 概要：通常の単体圏上の全解像の係数射（Dwyer–Kan）。
方針：元の単体圏表示同値に沿って同じ自然変換を移す。
規約：元の全単体的解像を使う。
使われ方：自由相対圏の解像へ係数関手を送る。 -/
def resolutionMap {X Y : C} (f : X ⟶ Y) :
    ComonadSimplicialResolution.diagram G X ⟶ ComonadSimplicialResolution.diagram G Y :=
  Functor.whiskerLeft _root_.SerrePositivity.SimplexPresentation.inverse.op (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.presentationMap G f)

/-- 概要：全解像の係数射の各成分は元の同じ冪の射（Dwyer–Kan）。
方針：表示同値・反対化・移送の成分を評価する。
規約：任意の単体次数で同じ式。
使われ方：係数関手の公理と augmentation の自然性。 -/
lemma resolutionMap_app {X Y : C} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ) :
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.resolutionMap G f).app n = _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f (n.unop.len + 1) := rfl

/-- 概要：全解像の係数射は恒等射を保つ（Dwyer–Kan）。
方針：各次数で元の冪の恒等則を使う。
規約：同じ自然変換の厳密な等式。
使われ方：全解像の係数関手の構成。 -/
lemma resolutionMap_id (X : C) : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.resolutionMap G (𝟙 X) = 𝟙 _ := by
  apply NatTrans.ext
  funext n
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap_id G X (n.unop.len + 1)

/-- 概要：全解像の係数射は合成を保つ（Dwyer–Kan）。
方針：各次数で元の冪の合成則を使う。
規約：同じ全単体作用素を保持する。
使われ方：相対関手の合成を解像へ送る。 -/
lemma resolutionMap_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.resolutionMap G (f ≫ g) = _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.resolutionMap G f ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.resolutionMap G g := by
  apply NatTrans.ext
  funext n
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap_comp G f g (n.unop.len + 1)

/-- 概要：全 augmentation は元の係数射に自然（Dwyer–Kan）。
方針：元の逐次合成の自然性を各次数で使う。
規約：元の全単体的 augmentation の同じ成分。
使われ方：係数関手による対象表示の保存。 -/
lemma resolutionMap_augmentation {X Y : C} (f : X ⟶ Y) :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.resolutionMap G f ≫ ComonadSimplicialResolution.augmentation G Y =
      ComonadSimplicialResolution.augmentation G X ≫ (Functor.const SimplexCategoryᵒᵖ).map f := by
  apply NatTrans.ext
  funext n
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.augmentation_naturality G f (n.unop.len + 1)

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution
