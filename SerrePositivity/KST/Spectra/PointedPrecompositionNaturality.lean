module

public import SerrePositivity.KST.Spectra.PointedPrecompositionAction
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSymmetry

/-!
概要：一つの源区間から移した前合成区間は、標的への後合成と区間全体で自然。
方針：普遍評価の転置と内部 Hom の交換の厳密自然性を比較する。
規約：対象ごとに区間を選び直さない。使われ方：符号反転の普遍区間の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 同じ点つき族の転置は、標的への後合成と厳密に可換。 -/
lemma transpose_post {A U V Z : PointedSimplicialSet.{u}}
    (f : A ⟶ PointedObject.basedHom U V) (v : V ⟶ Z) :
    transpose (f ≫ PointedObject.basedHomMap U v) =
      transpose f ≫ PointedObject.basedHomMap A v := by
  unfold transpose
  change curry ((β_ A U).hom ≫ uncurry (f ≫ (ihom U).map v)) =
    curry ((β_ A U).hom ≫ uncurry f) ≫ (ihom A).map v
  rw [uncurry_natural_right, ← Category.assoc, curry_natural_right]

/-- 源の射を前合成へ送る同じ実作用は、標的への後合成に関して自然。 -/
lemma preAction_post {W D C C' : PointedSimplicialSet.{u}} (v : C ⟶ C') :
    preAction W D C ≫ PointedObject.basedHomMap (PointedObject.basedHom D C)
        (PointedObject.basedHomMap W v) =
      preAction W D C' ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.basedHomMap D v)
        (PointedObject.basedHom W C') := by
  have he := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeTarget.natural_post W (PointedObject.basedHom D C) v
  have hr := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource.natural_pre_right W (PointedObject.basedHomMap D v) C'
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, PointedObject.ihom_obj_eq_basedHom] at he hr
  change PointedObject.basedHomMap W
      (PointedObject.basedHomMap (PointedObject.basedHom D C) v) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso W (PointedObject.basedHom D C) C').hom =
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso W (PointedObject.basedHom D C) C).hom ≫
      PointedObject.basedHomMap (PointedObject.basedHom D C)
        (PointedObject.basedHomMap W v) at he
  have ht : transpose (𝟙 (PointedObject.basedHom D C)) ≫
      PointedObject.basedHomMap (PointedObject.basedHom D C) v =
      transpose (𝟙 (PointedObject.basedHom D C')) ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.basedHomMap D v) C' := by
    rw [← transpose_post, Category.id_comp, ← transpose_pre_outer, Category.comp_id]
  unfold preAction
  rw [Category.assoc, ← he, ← Category.assoc]
  change ((ihom W).map (transpose (𝟙 (PointedObject.basedHom D C))) ≫
    (ihom W).map (PointedObject.basedHomMap (PointedObject.basedHom D C) v)) ≫ _ = _
  rw [← Functor.map_comp, ht, Functor.map_comp, Category.assoc, hr]
  rfl

/-- 同じ源区間の前合成像は、標的の後合成と実辺全体で厳密に可換。 -/
lemma VerticalPath.basedPre_post_path {W D C C' : PointedSimplicialSet.{u}}
    {f g : W ⟶ D} (P : VerticalPath (PointedObject.toPoint D) f g) (v : C ⟶ C') :
    ((P.basedPre C).basedPost (PointedObject.basedHomMap W v)).path =
      ((P.basedPre C').pre (PointedObject.basedHomMap D v)).path := by
  change (P.basedPre C).path ≫ _ = (P.basedPre C').path ≫ _
  rw [VerticalPath.basedPre_action_path, VerticalPath.basedPre_action_path]
  have h := preAction_post (W := W) (D := D) v
  simpa only [Under.comp_right, Category.assoc] using
    congrArg (fun k => P.path ≫ k.right) h

end SerrePositivity.KST.Spectra.PointedMapping
