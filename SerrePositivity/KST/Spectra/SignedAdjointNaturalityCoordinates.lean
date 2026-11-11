module

public import SerrePositivity.KST.Spectra.SignedAdjointCompositionPaths
public import SerrePositivity.KST.Spectra.PointedIntervalProjectedNaturality

/-!
概要：二重反転辺の前後合成を、実入力比較に使う同じ区間の制限へ照合する。
方針：通常円への射影の厳密自然性と、元の二重反転の実辺の自然性を使う。
規約：入力の厳密自然性を仮定しない。使われ方：二重反転辺の実自然性正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.SignedAdjointPaths
open LoopExchangePaths

/-- 通常円と Kan 円の二重内部 Hom への同じ標的後合成。 -/
def targetPost {Z Z' : PointedSimplicialSet.{u}} (v : Z ⟶ Z') : target Z ⟶ target Z' :=
  PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
    (PointedObject.basedHomMap CirclePower.space.{u} v)

/-- 外側の通常円への射影は標的後合成と厳密に可換。 -/
lemma projection_natural {Z Z' : PointedSimplicialSet.{u}} (v : Z ⟶ Z') :
    projection Z ≫ targetPost v = doublePost v ≫ projection Z' := by
  have h := (MonoidalClosed.pre CirclePower.unit.{u}).naturality
    (PointedObject.basedHomMap CirclePower.space.{u} v)
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at h
  exact h.symm

/-- 第二辺の実辺は、普遍反転辺に入力制限と射影を作用させた射そのもの。 -/
lemma secondPath_path {A Y Z : PointedSimplicialSet.{u}} [KanComplex Z.right]
    (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
    (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z) :
    (secondPath f g).path = ((reversalTwice Z).path ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (input f g) (doubleLoop Z)).right) ≫
        (PointedObject.basedHomMap A (projection Z)).right := rfl

/-- 第二辺の後合成は、同じ標的二重反転区間への移した入力の制限そのもの。 -/
lemma secondPath_post_path {A Y Z Z' : PointedSimplicialSet.{u}}
    [KanComplex Z.right] [KanComplex Z'.right]
    (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
    (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z) (v : Z ⟶ Z') :
    ((secondPath f g).basedPost (targetPost v)).path =
      (((reversalTwice Z').pre (input f g ≫ doublePost v)).basedPost (projection Z')).path := by
  change (secondPath f g).path ≫ (PointedObject.basedHomMap A (targetPost v)).right =
    ((reversalTwice Z').path ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (input f g ≫ doublePost v) (doubleLoop Z')).right) ≫
        (PointedObject.basedHomMap A (projection Z')).right
  rw [secondPath_path]
  exact PointedMapping.VerticalPath.projectedNaturality_map (reversalTwice Z).path
    (reversalTwice Z').path (input f g) (doublePost v) (projection Z) (projection Z')
    (targetPost v) (projection_natural v) (reversalTwice_natural v)

/-- 第二辺の入力制限も同じ普遍区間の合成入力への制限として照合する。 -/
lemma secondPath_pre_path {A A' Y Z : PointedSimplicialSet.{u}} [KanComplex Z.right]
    (f : A' ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
    (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z) (j : A ⟶ A') :
    ((secondPath f g).pre j).path =
      (((reversalTwice Z).pre (j ≫ input f g)).basedPost (projection Z)).path := by
  change (secondPath f g).path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j (target Z)).right =
    ((reversalTwice Z).path ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (j ≫ input f g) (doubleLoop Z)).right) ≫
        (PointedObject.basedHomMap A (projection Z)).right
  rw [secondPath_path]
  have hn := (MonoidalClosed.pre j).naturality (projection Z)
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hn
  change PointedObject.basedHomMap A' (projection Z) ≫
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j (target Z) =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j (doubleLoop Z) ≫
        PointedObject.basedHomMap A (projection Z) at hn
  have ht := congrArg (fun q => (reversalTwice Z).path ≫
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (input f g) (doubleLoop Z)).right ≫ q.right) hn
  simp only [Under.comp_right] at ht
  simp only [Category.assoc]
  rw [ht]
  have hc := congrArg (fun q => (reversalTwice Z).path ≫ q.right ≫
    (PointedObject.basedHomMap A (projection Z)).right)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp j (input f g) (doubleLoop Z))
  simpa only [Under.comp_right, Category.assoc] using hc

end SerrePositivity.KST.Spectra.SignedAdjointPaths
