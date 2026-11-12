module

public import SerrePositivity.KST.Spectra.PointedCotensorCoordinateHomotopies

/-!
概要：指定パラメータ上で一定な正方形を、自由パラメータ制限に垂直な実区間へ移す。
方針：制限の座標自然性を使い、元の全正方形の curry の定数性を移す。
規約：指定部分全体に垂直。使われ方：自由区間の両端を固定する構造区間。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedCotensorCoordinates
variable {K L : SSet.{u}} {T E : PointedSimplicialSet.{u}}
  {a b : K ⟶ (PointedObject.basedHom T E).right} (j : L ⟶ K) (H : SSet.Homotopy a b)
  (hrel : j ▷ (Δ[1] : SSet.{u}) ≫ H.h =
    fst L (Δ[1] : SSet.{u}) ≫ j ≫ a)

include hrel

/-- 元の正方形が指定パラメータ上で一定なら、移した実区間も制限射影後に一定。 -/
lemma intervalOfHomotopy_over :
    (intervalOfHomotopy H).path ≫ (PointedObject.basedHomMap T
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.adjoinFunctor.map j) E)).right =
    SSet.const (PointedMapping.familyVertex
      (family a ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.adjoinFunctor.map j) E)) := by
  apply (cancel_mono (iso L T E).hom).1
  rw [Category.assoc]
  erw [natural_parameter j T E]
  simp only [intervalOfHomotopy_path, Category.assoc, Iso.inv_hom_id_assoc]
  rw [SSet.const_comp, family_parameter, family_vertex, curry_pre_app, hrel,
    ExponentialPaths.curry_fst]

/-- 同じ実正方形を、指定した自由パラメータの制限に垂直な実区間へ移す。 -/
def relativeIntervalOfHomotopy : PointedMapping.VerticalPath
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.adjoinFunctor.map j) E)
    (family a) (family b) where
  path := (intervalOfHomotopy H).path
  zero := (intervalOfHomotopy H).zero
  one := (intervalOfHomotopy H).one
  «over» := intervalOfHomotopy_over j H hrel

end SerrePositivity.KST.Spectra.PointedCotensorCoordinates
