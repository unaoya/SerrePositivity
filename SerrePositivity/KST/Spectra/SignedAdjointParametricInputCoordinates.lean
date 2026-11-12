module

public import SerrePositivity.KST.Spectra.SignedAdjointFirstInputCoordinates
public import SerrePositivity.KST.Spectra.PointedProjectedIhomPath
public import SerrePositivity.KST.Spectra.PointedIntervalCotensorConjugation

/-!
概要：元の第一辺の内部 Hom 像を、射影後の同じ交換符号区間への合成入力へ戻す。
方針：端点の表示が異なる同じ実辺を抽象補題で照合し、前後合成の自然性を使う。
規約：選択済み区間を展開しない。使われ方：第一辺の全族実入力比較の終辺。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.SignedAdjointPaths
open LoopExchangePaths

/-- 全族内部 Hom に移した元の第一辺への入力は、同じ射影後区間への合成入力。 -/
lemma firstPath_ihom_pre_path {P A A' Y Z W : PointedSimplicialSet.{u}}
    [KanComplex Z.right] [KanComplex W.right]
    (a : Z ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} W)
    (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right)
    (f : A' ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
    (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z)
    (j : A ⟶ PointedObject.basedHom P A') :
    (((firstPath a ha f g).basedIhomMap P).pre j).path =
      (((((cancellationFirst a ha).basedIhomMap P).basedPost
        (PointedObject.basedHomMap P (projection Z))).pre
          (j ≫ PointedObject.basedHomMap P (input f g))).path) := by
  have he := PointedMapping.VerticalPath.basedIhomMap_path_congr
    (firstPath a ha f g) (((cancellationFirst a ha).pre (input f g)).basedPost (projection Z))
    P rfl
  exact (congrArg (· ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j _).right) he).trans
    (PointedMapping.VerticalPath.projectedIhomPre_path
      (cancellationFirst a ha) (input f g) (projection Z) P j)

end SerrePositivity.KST.Spectra.SignedAdjointPaths
