module

public import SerrePositivity.KST.Spectra.PointedBasedPathComposition

/-!
概要：区間全体の射影一致を、前合成・懸垂・厳密な後合成正方形へ移す。
方針：元の内部 Hom の実際の可換正方形を、同じ区間族へ後合成する。
規約：Kan 性不要。使われ方：構造比較の三辺の射影を境界の帰納三角形へ同定する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.PointedMapping.VerticalPath
variable {T E F : PointedSimplicialSet.{u}} {f g : T ⟶ E} {f' g' : T ⟶ F}
  (P : VerticalPath (PointedObject.toPoint E) f g)
  (Q : VerticalPath (PointedObject.toPoint F) f' g') (p : E ⟶ F)
  (h : P.path ≫ (PointedObject.basedHomMap T p).right = Q.path)

include h in
/-- 全区間の射影一致は、端点表示が異なっても同じ一次単体の一致を与える。 -/
lemma projection_edge_value :
    (P.edge.map (PointedObject.basedHomMap T p).right).edge = Q.edge.edge := by
  change (PointedObject.basedHomMap T p).right.app _ (SSet.yonedaEquiv P.path) =
    SSet.yonedaEquiv Q.path
  rw [← SSet.yonedaEquiv_comp, h]

include h in
/-- 元の射影一致は、同じ源の前合成後も全区間で一致する。 -/
lemma pre_projection_path {U : PointedSimplicialSet.{u}} (i : U ⟶ T) :
    (P.pre i).path ≫ (PointedObject.basedHomMap U p).right = (Q.pre i).path := by
  have hs : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i E ≫ PointedObject.basedHomMap U p =
      PointedObject.basedHomMap T p ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i F := by
    simp only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
    exact ((MonoidalClosed.pre i).naturality p).symm
  have he := congrArg Under.Hom.right hs
  change (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i E).right ≫ (PointedObject.basedHomMap U p).right =
    (PointedObject.basedHomMap T p).right ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i F).right at he
  change (P.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i E).right) ≫ _ = Q.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i F).right
  rw [Category.assoc, he, ← Category.assoc, h]

include h in
/-- 同じ射影区間を懸垂しても、元の懸垂 Hom の射の自然性により全区間で一致する。 -/
lemma suspension_projection_path :
    P.suspension.forgetProjection.path ≫
      (PointedObject.basedHomMap (PointedSimplicialSet.circle.{u} ⊗ T)
        (PointedSimplicialSet.circle.{u} ◁ p)).right =
        Q.suspension.forgetProjection.path := by
  have hs := (RawSpectrumMapping.suspensionHom_post_pointed T p).symm
  have he := congrArg Under.Hom.right hs
  change (suspensionHom T E).right ≫
      (PointedObject.basedHomMap (PointedSimplicialSet.circle.{u} ⊗ T)
        (PointedSimplicialSet.circle.{u} ◁ p)).right =
    (PointedObject.basedHomMap T p).right ≫ (suspensionHom T F).right at he
  change (P.path ≫ (suspensionHom T E).right) ≫ _ = Q.path ≫ (suspensionHom T F).right
  rw [Category.assoc, he, ← Category.assoc, h]

include h in
/-- 射影と可換な後合成正方形は、同じ区間の射影一致をそのまま保持する。 -/
lemma post_projection_path {E' F' : PointedSimplicialSet.{u}}
    (p' : E' ⟶ F') (v : E ⟶ E') (w : F ⟶ F') (hs : v ≫ p' = p ≫ w) :
    (P.basedPost v).path ≫ (PointedObject.basedHomMap T p').right =
      (Q.basedPost w).path := by
  have hmap : PointedObject.basedHomMap T v ≫ PointedObject.basedHomMap T p' =
      PointedObject.basedHomMap T p ≫ PointedObject.basedHomMap T w := by
    change (ihom T).map v ≫ (ihom T).map p' = (ihom T).map p ≫ (ihom T).map w
    rw [← Functor.map_comp, ← Functor.map_comp, hs]
  have he := congrArg Under.Hom.right hmap
  change (PointedObject.basedHomMap T v).right ≫ (PointedObject.basedHomMap T p').right =
    (PointedObject.basedHomMap T p).right ≫ (PointedObject.basedHomMap T w).right at he
  change (P.path ≫ (PointedObject.basedHomMap T v).right) ≫ _ =
    Q.path ≫ (PointedObject.basedHomMap T w).right
  rw [Category.assoc, he, ← Category.assoc, h]

end SerrePositivity.KST.Spectra.PointedMapping.VerticalPath
