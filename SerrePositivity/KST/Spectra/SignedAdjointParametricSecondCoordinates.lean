module

public import SerrePositivity.KST.Spectra.SignedAdjointParametricCoordinates
public import SerrePositivity.KST.Spectra.SignedAdjointParametricInputCoordinates
public import SerrePositivity.KST.Spectra.ParametricLoopReversalPaths

/-!
概要：元の第二辺の全族後合成と内部 Hom 像を、同じ普遍二重反転区間へ照合する。
方針：実辺全体の厳密全族自然性と、入力・射影の内部 Hom 座標を使う。
規約：元の区間選択を保持。使われ方：第一・第二辺の共有境界付き実自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.SignedAdjointPaths
open LoopExchangePaths

/-- 元の第二辺の全族後合成は、同じ標的区間の内部 Hom 像への合成入力制限。 -/
lemma secondPath_parametric_post_path {P A Y Z Z' : PointedSimplicialSet.{u}}
    [KanComplex Z.right] [KanComplex Z'.right]
    (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
    (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z)
    (v : P ⟶ PointedObject.basedHom Z Z') :
    ((secondPath f g).basedPost (targetParametricPost v)).path =
      (((((reversalTwice Z').basedIhomMap P).pre
        (input f g ≫ doubleParametricPost v)).basedPost
          (PointedObject.basedHomMap P (projection Z'))).path) := by
  change (secondPath f g).path ≫
      (PointedObject.basedHomMap A (targetParametricPost v)).right =
    ((((reversalTwice Z').basedIhomMap P).path ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (input f g ≫ doubleParametricPost v)
        (PointedObject.basedHom P (doubleLoop Z'))).right) ≫
          (PointedObject.basedHomMap A (PointedObject.basedHomMap P (projection Z'))).right)
  rw [secondPath_path]
  exact PointedMapping.VerticalPath.projectedNaturality_map (reversalTwice Z).path
    ((reversalTwice Z').basedIhomMap P).path (input f g) (doubleParametricPost v)
    (projection Z) (PointedObject.basedHomMap P (projection Z')) (targetParametricPost v)
    (projection_parametric v) (reversalTwice_parametric v)

/-- 元の第二辺の全族内部 Hom 像も、同じ射影後区間への合成入力制限。 -/
lemma secondPath_ihom_pre_path {P A A' Y Z : PointedSimplicialSet.{u}}
    [KanComplex Z.right]
    (f : A' ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
    (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z)
    (j : A ⟶ PointedObject.basedHom P A') :
    (((secondPath f g).basedIhomMap P).pre j).path =
      (((((reversalTwice Z).basedIhomMap P).basedPost
        (PointedObject.basedHomMap P (projection Z))).pre
          (j ≫ PointedObject.basedHomMap P (input f g))).path) := by
  have he := PointedMapping.VerticalPath.basedIhomMap_path_congr
    (secondPath f g) (((reversalTwice Z).pre (input f g)).basedPost (projection Z)) P rfl
  exact (congrArg (· ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j _).right) he).trans
    (PointedMapping.VerticalPath.projectedIhomPre_path
      (reversalTwice Z) (input f g) (projection Z) P j)

end SerrePositivity.KST.Spectra.SignedAdjointPaths
