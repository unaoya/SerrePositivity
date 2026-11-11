module

public import SerrePositivity.KST.Spectra.PointedPrecompositionSourceNaturality
public import SerrePositivity.KST.Spectra.PointedVerticalPathFiber

/-!
概要：射影を固定する入力区間は、その射影を経由する族への前合成では全区間が一定。
方針：前合成作用の頂点式と厳密な源自然性を、同じ実辺全体に適用する。
規約：端点だけから一定性を推論しない。使われ方：交換の自然性正方形の両端境界。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 同じ前合成作用の頂点は、元の同じ射による前合成を表す。 -/
lemma preAction_vertex {W D : PointedSimplicialSet.{u}} (f : W ⟶ D)
    (E : PointedSimplicialSet.{u}) :
    (preAction W D E).right.app _ (familyVertex f) = familyVertex (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed f E) := by
  change (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso W (PointedObject.basedHom D E) E).hom.right.app _
    ((PointedObject.basedHomMap W (transpose (𝟙 (PointedObject.basedHom D E)))).right.app _
      (familyVertex f)) = _
  rw [familyVertex_post, ← familyVertex_transpose, transpose_evaluation_pre]

/-- 一定の実辺を前合成へ移しても、始点の同じ前合成頂点で全区間が一定。 -/
lemma VerticalPath.basedPre_path_const {W D : PointedSimplicialSet.{u}} {a b : W ⟶ D}
    (H : VerticalPath (PointedObject.toPoint D) a b)
    (h : H.path = SSet.const (familyVertex a)) (E : PointedSimplicialSet.{u}) :
    (H.basedPre E).path = SSet.const (familyVertex (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a E)) := by
  rw [VerticalPath.basedPre_action_path, h, SSet.const_comp, preAction_vertex]

/-- 一定の実辺を評価したホモトピーは、元の始点の射で全区間が一定。 -/
lemma VerticalPath.homotopy_h_of_path_const {A E C : PointedSimplicialSet.{u}}
    {p : E ⟶ C} {f g : A ⟶ E} (H : VerticalPath p f g)
    (h : H.path = SSet.const (familyVertex f)) :
    H.homotopy.h = fst A.right (Δ[1] : SSet.{u}) ≫ f.right := by
  rw [VerticalPath.homotopy_h, h, uncurry_const_familyVertex]

/-- 射影固定の同じ区間は、その射影を経由する全入力族への前合成では一定。 -/
lemma VerticalPath.basedPre_projection_constant {A B C : PointedSimplicialSet.{u}}
    {p : B ⟶ C} {a b : A ⟶ B} (H : VerticalPath p a b)
    (E : PointedSimplicialSet.{u}) :
    ((H.forgetProjection.basedPre E).pre (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed p E)).homotopy.h =
      fst (PointedObject.basedHom C E).right (Δ[1] : SSet.{u}) ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (a ≫ p) E).right := by
  have hc : (H.forgetProjection.basedPost p).path =
      SSet.const (familyVertex (a ≫ p)) := H.over
  have hk := (H.forgetProjection.basedPost p).basedPre_path_const hc E
  rw [VerticalPath.homotopy_h, ← VerticalPath.basedPre_post_input_path, hk,
    uncurry_const_familyVertex]

end SerrePositivity.KST.Spectra.PointedMapping
