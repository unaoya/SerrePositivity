module

public import SerrePositivity.KST.Spectra.PointedIntervalConjugateSquare
public import SerrePositivity.KST.Spectra.PointedPrecompositionParametricNaturality

/-!
概要：同じ実辺の厳密自然性と前合成区間の内部 Hom 像を、交換同型で共役する。
方針：同じ座標射の前後合成を使い、同型の逆射で元の実辺の等式を打ち消す。
規約：ホモトピー充填を新たに選ばない。使われ方：二重反転辺の全族自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.PointedMapping.VerticalPath

/-- 実辺全体の厳密自然性は、同じ同型による共役後にも厳密自然性となる。 -/
lemma conjugate_natural_path {A A' B B' : PointedSimplicialSet.{u}}
    {a b : A ⟶ A} {c d : B ⟶ B}
    (R : VerticalPath (PointedObject.toPoint A) a b)
    (T : VerticalPath (PointedObject.toPoint B) c d)
    (v : A ⟶ B) (e : A ≅ A') (f : B ≅ B') (w : A' ⟶ B')
    (hc : e.hom ≫ w = v ≫ f.hom)
    (hn : (R.basedPost v).path = (T.pre v).path) :
    ((((R.basedPost e.hom).pre e.inv).basedPost w).path) =
      ((((T.basedPost f.hom).pre f.inv).pre w).path) := by
  rw [coordinate_post_path R e f v w hc,
    coordinate_pre_path T e f v w (conjugateSquare_inverse v e f w hc), hn]

/-- 前合成区間の内部 Hom 像は、同じ交換同型で共役した前合成区間と実辺全体で一致。 -/
lemma basedPre_ihom_conjugate_path {A : PointedSimplicialSet.{u}} {a b : A ⟶ A}
    (R : VerticalPath (PointedObject.toPoint A) a b) (K Z : PointedSimplicialSet.{u}) :
    (((R.basedPre (PointedObject.basedHom K Z)).basedPost
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A K Z).hom).pre (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A K Z).inv).path =
      ((R.basedPre Z).basedIhomMap K).path := by
  let e := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A K Z
  let V := (ihom K).obj (PointedObject.basedHom A Z)
  have h := R.basedPre_cotensor_exchange_path K Z
  change (R.basedPre (PointedObject.basedHom K Z)).path ≫
      (PointedObject.basedHomMap (PointedObject.basedHom A (PointedObject.basedHom K Z))
        e.hom).right =
    ((R.basedPre Z).basedIhomMap K).path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed e.hom V).right at h
  have hp : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed e.hom V ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed e.inv V = 𝟙 _ := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.preIso, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre,
      PointedObject.ihom_obj_eq_basedHom] using (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.preIso e V).hom_inv_id
  have ht := congrArg (· ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed e.inv V).right) h
  change ((R.basedPre (PointedObject.basedHom K Z)).path ≫
    (PointedObject.basedHomMap _ e.hom).right) ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed e.inv V).right = _
  have hp' : (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed e.hom V).right ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed e.inv V).right = 𝟙 _ := by
    exact (congrArg Under.Hom.right hp).trans (by rfl)
  exact ht.trans (by
    rw [Category.assoc, hp']
    exact Category.comp_id _)

end SerrePositivity.KST.Spectra.PointedMapping.VerticalPath
