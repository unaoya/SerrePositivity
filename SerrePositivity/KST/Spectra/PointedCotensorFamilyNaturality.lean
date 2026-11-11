module

public import SerrePositivity.KST.Spectra.PointedCotensorCoordinateFamilies

/-!
概要：通常の族を cotensor 値の射へ移す構成の三変数の厳密自然性。
方針：座標同型の自然性を元の族の頂点で評価する。
規約：点ごとの成分の等式は使わない。使われ方：自由区間の端点と構造射の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra

/-- 通常の族の指数頂点は、標的への後合成と可換。 -/
lemma ExponentialPaths.vertex_post {K E V : SSet.{u}} (a : K ⟶ E) (f : E ⟶ V) :
    ((ihom K).map f).app _ (ExponentialPaths.vertex a) = ExponentialPaths.vertex (a ≫ f) := by
  simp only [ExponentialPaths.vertex]
  rw [← SSet.yonedaEquiv_comp, ← curry_natural_right, Category.assoc]

namespace PointedCotensorCoordinates

/-- 自由パラメータ族の移送は、点つき源の制限と厳密に可換。 -/
lemma family_source {K : SSet.{u}} {T U E : PointedSimplicialSet.{u}}
    (i : T ⟶ U) (a : K ⟶ (PointedObject.basedHom U E).right) :
    i ≫ family a = family (a ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i E).right) := by
  apply ext
  rw [← PointedMapping.familyVertex_pre, family_vertex]
  have h := congrArg (fun q => q.app (Opposite.op ⦋0⦌)
    (PointedMapping.familyVertex (family a))) (natural_source K i E)
  simp only [NatTrans.comp_app_apply] at h
  rw [family_vertex, ExponentialPaths.vertex_post] at h
  exact h

/-- 自由パラメータ族の移送は、標的への後合成と厳密に可換。 -/
lemma family_target {K : SSet.{u}} {T E V : PointedSimplicialSet.{u}}
    (a : K ⟶ (PointedObject.basedHom T E).right) (f : E ⟶ V) :
    family a ≫ PointedObject.basedHomMap (PointedObject.adjoin K) f =
      family (a ≫ (PointedObject.basedHomMap T f).right) := by
  apply ext
  rw [← PointedMapping.familyVertex_post, family_vertex]
  have h := congrArg (fun q => q.app (Opposite.op ⦋0⦌)
    (PointedMapping.familyVertex (family a))) (natural_target K T f)
  simp only [NatTrans.comp_app_apply] at h
  rw [family_vertex, ExponentialPaths.vertex_post] at h
  exact h

/-- 自由パラメータの制限は、元の族への同じ前合成そのもの。 -/
lemma family_parameter {K L : SSet.{u}} {T E : PointedSimplicialSet.{u}}
    (j : L ⟶ K) (a : K ⟶ (PointedObject.basedHom T E).right) :
    family a ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.adjoinFunctor.map j) E =
      family (j ≫ a) := by
  apply ext
  rw [← PointedMapping.familyVertex_post, family_vertex]
  have h := congrArg (fun q => q.app (Opposite.op ⦋0⦌)
    (PointedMapping.familyVertex (family a))) (natural_parameter j T E)
  simp only [NatTrans.comp_app_apply] at h
  erw [family_vertex a, ExponentialPaths.vertex_pre j a] at h
  exact h

end PointedCotensorCoordinates
end SerrePositivity.KST.Spectra
