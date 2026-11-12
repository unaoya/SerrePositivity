module

public import SerrePositivity.KST.Spectra.PointedCotensorCoordinateFamilies
public import SerrePositivity.KST.Spectra.PointedHomTransposeComponents
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSymmetry

/-!
概要：座標同型で移した通常の族を、自由基点の随伴と点つき転置で明示する。
方針：元の成分への制限を頂点で計算し、二つの交換を打ち消す。
規約：全パラメータ族を保つ厳密等式。使われ方：自由区間の端点評価。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra

/-- 自由基点からの点つき族の頂点を制限すると、元の通常の族の指数頂点になる。 -/
lemma FreePointedHomRestriction.restrict_familyVertex {K : SSet.{u}}
    {Y : PointedSimplicialSet.{u}} (F : PointedObject.adjoin K ⟶ Y) :
    (FreePointedHomRestriction.restrict K Y).app _ (PointedMapping.familyVertex F) =
      ExponentialPaths.vertex (PointedObject.adjoinHomEquiv K Y F) := by
  change (FreePointedHomRestriction.restrict K Y).app _
    (SSet.yonedaEquiv (PointedMapping.pointFamily F)) = _
  rw [← SSet.yonedaEquiv_comp]
  apply congrArg SSet.yonedaEquiv
  rw [FreePointedHomRestriction.restrict, ← Category.assoc,
    PointedMapping.pointFamily, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι, curry_pre_app,
    whiskerRight_fst_assoc]
  rfl

namespace PointedCotensorCoordinates

/-- 座標同型の逆で作った族は、自由基点の随伴で移して転置した同じ射。 -/
lemma family_eq_transpose {K : SSet.{u}} {T E : PointedSimplicialSet.{u}}
    (a : K ⟶ (PointedObject.basedHom T E).right) :
    family a = PointedMapping.transpose
      ((PointedObject.adjoinHomEquiv K (PointedObject.basedHom T E)).symm a) := by
  apply ext
  rw [family_vertex, PointedMapping.familyVertex_transpose]
  symm
  have hh : (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (PointedObject.adjoin K) T E).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso T (PointedObject.adjoin K) E).hom = 𝟙 _ := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.hom_eq_inv, Iso.inv_hom_id]
  have h := congrArg Under.Hom.right hh
  simp only [Under.comp_right, Under.id_right] at h
  change ((_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (PointedObject.adjoin K) T E).hom.right ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso T (PointedObject.adjoin K) E).hom.right ≫
    FreePointedHomRestriction.restrict K (PointedObject.basedHom T E)).app _
      (PointedMapping.familyVertex _) = _
  rw [← Category.assoc, h, Category.id_comp]
  erw [FreePointedHomRestriction.restrict_familyVertex
    ((PointedObject.adjoinHomEquiv K (PointedObject.basedHom T E)).symm a)]
  rw [Equiv.apply_symm_apply]

end PointedCotensorCoordinates
end SerrePositivity.KST.Spectra
