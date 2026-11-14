module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RoofSliceTransport

/-! # 実 over 辺の指定合成三角形

概要：点上の over slice の一単体を、元の単体集合の二単体として表示する。
方針：Δ[1] と点の join を Δ[2] に戻し、三面を元の射影と回収辺に照合する。
規約：任意の単体集合で成立する。使われ方：実分母の細分射に対する二対三性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 実 over の一単体が指定する、元の二単体。 -/
def roofPointSliceTriangle {X : SSet.{u}} (a : Δ[0] ⟶ X) (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋1⦌) :
    Δ[2] ⟶ X := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).inv ≫ σ.val

/-- 実 over の一単体の二面は、始域への射影の一単体。 -/
lemma roofPointSliceTriangle_base {X : SSet.{u}} (a : Δ[0] ⟶ X)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋1⦌) :
    SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ roofPointSliceTriangle a σ) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection a).app (Opposite.op ⦋1⦌) σ := by
  change SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).inv ≫ σ.val)) = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_one_inl, Category.assoc, Iso.hom_inv_id_assoc]
  rfl

/-- 実 over の一単体の零面・一面は、両端から回収した指定実辺。 -/
lemma roofPointSliceTriangle_leg {X : SSet.{u}} (a : Δ[0] ⟶ X)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋1⦌) (i : Fin 2) :
    SSet.yonedaEquiv (stdSimplex.δ i.castSucc ≫ roofPointSliceTriangle a σ) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).δ i σ)).edge := by
  have h : stdSimplex.δ i.castSucc ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).inv =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ i) (𝟙 Δ[0]) := by
    apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_one_vertex, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change SSet.yonedaEquiv (stdSimplex.δ i.castSucc ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).inv ≫ σ.val)) =
    SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ i) (𝟙 Δ[0]) ≫ σ.val))
  rw [← Category.assoc, h, Category.assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
