module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.StrictCoconeLegTriangles
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedSlice

/-!
概要：余錐の実際の合成二単体を、元の図式の辺と頂点の join から切り出す形状。
方針：標準 join 同型と元の辺を使い、最後の頂点と元の二単体を厳密に回収する。
規約：元の合成二単体そのものを保持。使われ方：native span の普遍全 Hom の三角形族。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {K : SSet.{u}} {a b : K _⦋0⦌} (e : K.Edge a b)

/-- 元の図式の辺と余錐頂点の join を、実際の標準二単体で表示する形状。 -/
def coconeLegTriangleShape : (Δ[2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0] :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm e.edge) (𝟙 Δ[0])

/-- この形状の最後の頂点は、元の余錐頂点の同じ右包含そのもの。 -/
lemma coconeLegTriangleShape_tip :
    (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)) ≫ coconeLegTriangleShape e =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0] := by
  have h : (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) :
      (Δ[0] : SSet.{u}) ⟶ Δ[2]) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[1] Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_inr_vertex]
    apply SSet.yonedaEquiv.injective
    decide
  rw [coconeLegTriangleShape, ← Category.assoc, h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]

/-- 切り出した図式は、元の余錐の脚の実際の合成二単体そのもの。 -/
lemma coconeLegTriangleShape_diagram {X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    coconeLegTriangleShape e ≫ c.val =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexLegCompStruct c e).simplex := by
  change _ = SSet.yonedaEquiv.symm (SSet.yonedaEquiv
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm e.edge) (𝟙 Δ[0]) ≫ c.val))
  rw [Equiv.symm_apply_apply]
  exact Category.assoc _ _ _

/-- 脚の両端を正規化した同じ合成二単体も、元の同じ join 形状で切り出される。 -/
lemma coconeLegTriangleShape_normalized_diagram {X : SSet.{u}} {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) {z₀ z₁ : X _⦋0⦌}
    (h₀ : p.app (Opposite.op ⦋0⦌) a = z₀) (h₁ : p.app (Opposite.op ⦋0⦌) b = z₁)
    (k : X.Edge z₀ z₁) (hk : k.edge = (e.map p).edge) :
    coconeLegTriangleShape e ≫ c.val =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeVertexLegAtCompStruct c e h₀ h₁ k hk).simplex :=
  coconeLegTriangleShape_diagram e c

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
