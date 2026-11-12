module

public import SerrePositivity.KST.Spectra.PointedIhomIntervalNaturality
public import SerrePositivity.KST.Spectra.PointedIntervalConjugateSquare

/-!
概要：元の区間の同型による共役と、パラメータ内部 Hom への作用を実辺全体で交換する。
方針：同じ同型を内部 Hom に移し、元の前後合成と内部 Hom の厳密交換則を用いる。
規約：区間を選び直さない。使われ方：通常円の交換区間の全族自然性の座標変更。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 同じ点つき同型を、全パラメータを保持した内部 Hom の同型へ移す。 -/
def cotensorIso (K : PointedSimplicialSet.{u}) {A A' : PointedSimplicialSet.{u}} (e : A ≅ A') :
    PointedObject.basedHom K A ≅ PointedObject.basedHom K A' where
  hom := PointedObject.basedHomMap K e.hom
  inv := PointedObject.basedHomMap K e.inv
  hom_inv_id := by
    change (ihom K).map e.hom ≫ (ihom K).map e.inv = _
    rw [← CategoryTheory.Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id]
    simp only [PointedObject.ihom_obj_eq_basedHom]
  inv_hom_id := by
    change (ihom K).map e.inv ≫ (ihom K).map e.hom = _
    rw [← CategoryTheory.Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id]
    simp only [PointedObject.ihom_obj_eq_basedHom]

/-- 実辺全体の一致は、同じ内部 Hom の作用でも保持される。端点表示は異なってよい。 -/
lemma VerticalPath.basedIhomMap_path_congr {A E : PointedSimplicialSet.{u}}
    {f g f' g' : A ⟶ E} (R : VerticalPath (PointedObject.toPoint E) f g)
    (S : VerticalPath (PointedObject.toPoint E) f' g') (K : PointedSimplicialSet.{u})
    (h : R.path = S.path) : (R.basedIhomMap K).path = (S.basedIhomMap K).path := by
  rw [basedIhomMap_path, basedIhomMap_path, h]

/-- 共役した元の区間の内部 Hom 像は、同じ内部 Hom 同型で共役した実辺そのもの。 -/
lemma VerticalPath.basedIhomMap_conjugate_path {A A' : PointedSimplicialSet.{u}}
    {f g : A ⟶ A} (R : VerticalPath (PointedObject.toPoint A) f g)
    (K : PointedSimplicialSet.{u}) (e : A ≅ A') :
    ((((R.basedPost e.hom).pre e.inv).basedIhomMap K)).path =
      ((((R.basedIhomMap K).basedPost (cotensorIso K e).hom).pre (cotensorIso K e).inv)).path := by
  have h := congrArg (· ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.basedHomMap K e.inv)
    (PointedObject.basedHom K A')).right) (R.basedIhomMap_post_path K e.hom)
  exact ((R.basedPost e.hom).basedIhomMap_pre_path_natural K e.inv).trans h

end SerrePositivity.KST.Spectra.PointedMapping
