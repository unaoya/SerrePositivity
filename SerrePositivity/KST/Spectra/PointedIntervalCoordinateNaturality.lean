module

public import SerrePositivity.KST.Spectra.PointedBasedPathCalculus

/-!
概要：実区間の前後合成を、同型による座標変更の同じ Hom 射へ照合する。
方針：内部 Hom の制限・後合成の自然性を同じ実辺へ作用させる。
規約：区間を再選択しない。使われ方：全族の自然性正方形を三重 loop 座標へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 同じ Hom の族を、元の前合成・後合成で新しい座標へ移す点つき射。 -/
def coordinateMap {A A' B B' : PointedSimplicialSet.{u}} (i : A' ⟶ A) (j : B ⟶ B') :
    PointedObject.basedHom A B ⟶ PointedObject.basedHom A' B' :=
  PointedObject.basedHomMap A j ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i B'

private lemma closed_coordinate_post {C : Type*} [Category C] [MonoidalCategory C]
    [MonoidalClosed C] {A A' B B' : C} (i : A' ⟶ A) (x : A ⟶ A')
    (j : B ⟶ B') (v : A ⟶ B) (w : A' ⟶ B') (h : x ≫ w = v ≫ j) :
    ((ihom A).map x ≫ (MonoidalClosed.pre i).app A') ≫ (ihom A').map w =
      (ihom A).map v ≫ ((ihom A).map j ≫ (MonoidalClosed.pre i).app B') := by
  rw [Category.assoc, ← (MonoidalClosed.pre i).naturality w,
    ← Category.assoc, ← Functor.map_comp, h, Functor.map_comp, Category.assoc]

private lemma closed_coordinate_pre {C : Type*} [Category C] [MonoidalCategory C]
    [MonoidalClosed C] {A A' B B' : C} (i : A' ⟶ A) (j : B ⟶ B')
    (k : B' ⟶ B) (v : A ⟶ B) (w : A' ⟶ B') (h : w ≫ k = i ≫ v) :
    ((ihom B).map j ≫ (MonoidalClosed.pre k).app B') ≫
        (MonoidalClosed.pre w).app B' =
      (MonoidalClosed.pre v).app B ≫
        ((ihom A).map j ≫ (MonoidalClosed.pre i).app B') := by
  have hp (X Y T : C) [Closed X] [Closed Y] [Closed T]
      (f : X ⟶ Y) (g : Y ⟶ T) (U : C) :
      (MonoidalClosed.pre g).app U ≫ (MonoidalClosed.pre f).app U =
        (MonoidalClosed.pre (f ≫ g)).app U :=
    (congrArg (fun q => q.app U) (MonoidalClosed.pre_map f g)).symm
  rw [Category.assoc, hp, h, ← hp,
    ← Category.assoc, (MonoidalClosed.pre v).naturality j, Category.assoc]

/-- 座標を変えて後合成する区間は、元の後合成区間の同じ座標像。 -/
lemma VerticalPath.coordinate_post_path {A A' B B' : PointedSimplicialSet.{u}}
    {f g : A ⟶ A} (P : VerticalPath (PointedObject.toPoint A) f g)
    (e : A ≅ A') (d : B ≅ B') (v : A ⟶ B) (w : A' ⟶ B')
    (h : e.hom ≫ w = v ≫ d.hom) :
    ((((P.basedPost e.hom).pre e.inv).basedPost w).path) =
      (P.basedPost v).path ≫ (coordinateMap e.inv d.hom).right := by
  change ((P.path ≫ (PointedObject.basedHomMap A e.hom).right) ≫
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed e.inv A').right) ≫ (PointedObject.basedHomMap A' w).right =
      (P.path ≫ (PointedObject.basedHomMap A v).right) ≫ _
  have hc := closed_coordinate_post e.inv e.hom d.hom v w h
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hc
  change (PointedObject.basedHomMap A e.hom ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed e.inv A') ≫
      PointedObject.basedHomMap A' w = PointedObject.basedHomMap A v ≫
        (PointedObject.basedHomMap A d.hom ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed e.inv B') at hc
  simpa only [coordinateMap, Under.comp_right, Category.assoc,
    PointedObject.ihom_obj_eq_basedHom] using congrArg (fun q => P.path ≫ q.right) hc

/-- 同じ逆座標の前合成も、元の入力制限区間の同じ座標像。 -/
lemma VerticalPath.coordinate_pre_path {A A' B B' : PointedSimplicialSet.{u}}
    {f g : B ⟶ B} (Q : VerticalPath (PointedObject.toPoint B) f g)
    (e : A ≅ A') (d : B ≅ B') (v : A ⟶ B) (w : A' ⟶ B')
    (h : w ≫ d.inv = e.inv ≫ v) :
    ((((Q.basedPost d.hom).pre d.inv).pre w).path) =
      (Q.pre v).path ≫ (coordinateMap e.inv d.hom).right := by
  change ((Q.path ≫ (PointedObject.basedHomMap B d.hom).right) ≫
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed d.inv B').right) ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed w B').right =
      (Q.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed v B).right) ≫ _
  have hc := closed_coordinate_pre e.inv d.hom d.inv v w h
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hc
  change (PointedObject.basedHomMap B d.hom ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed d.inv B') ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed w B' = _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed v B ≫
        (PointedObject.basedHomMap A d.hom ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed e.inv B') at hc
  simpa only [coordinateMap, Under.comp_right, Category.assoc,
    PointedObject.ihom_obj_eq_basedHom] using congrArg (fun q => Q.path ≫ q.right) hc

end SerrePositivity.KST.Spectra.PointedMapping
