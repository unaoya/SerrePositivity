module

public import SerrePositivity.KST.Spectra.SignedAdjointFirstPostNaturality

/-!
概要：元の第一辺の入力制限を、同じ標的交換区間の射影後の合成入力制限へ照合する。
方針：内部 Hom の前後合成の自然性を元の実辺の射へ作用させる。
規約：具体的な区間の充填を展開しない。使われ方：第一辺の実入力正方形の終辺照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.SignedAdjointPaths
open LoopExchangePaths
variable {A A' Y Z W : PointedSimplicialSet.{u}} [KanComplex Z.right] [KanComplex W.right]
  (a : Z ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} W)
  (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right)
  (f : A' ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
  (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z)

/-- 元の第一辺は、同じ交換符号の実辺への入力制限と射影の合成。 -/
lemma firstPath_path : (firstPath a ha f g).path =
    ((cancellationFirst a ha).path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (input f g) (doubleLoop Z)).right) ≫
      (PointedObject.basedHomMap A' (projection Z)).right := rfl

/-- 元の第一辺への前合成は、射影後の同じ交換符号区間への合成入力の制限。 -/
lemma firstPath_pre_path (j : A ⟶ A') :
    ((firstPath a ha f g).pre j).path =
      ((((cancellationFirst a ha).basedPost (projection Z)).pre (j ≫ input f g)).path) := by
  change (firstPath a ha f g).path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j (target Z)).right =
    ((cancellationFirst a ha).path ≫
      (PointedObject.basedHomMap (doubleLoop Z) (projection Z)).right) ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (j ≫ input f g) (target Z)).right
  rw [firstPath_path]
  have hn := (MonoidalClosed.pre (input f g)).naturality (projection Z)
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hn
  change PointedObject.basedHomMap (doubleLoop Z) (projection Z) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (input f g) (target Z) =
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (input f g) (doubleLoop Z) ≫
      PointedObject.basedHomMap A' (projection Z) at hn
  have he := congrArg (fun m => (cancellationFirst a ha).path ≫ m.right ≫
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j (target Z)).right) hn
  simp only [Under.comp_right, Category.assoc] at he
  simp only [Category.assoc]
  rw [← he]
  have hc := congrArg (fun m => ((cancellationFirst a ha).path ≫
    (PointedObject.basedHomMap (doubleLoop Z) (projection Z)).right) ≫ m.right)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp j (input f g) (target Z))
  simpa only [Under.comp_right, Category.assoc] using hc

end SerrePositivity.KST.Spectra.SignedAdjointPaths
