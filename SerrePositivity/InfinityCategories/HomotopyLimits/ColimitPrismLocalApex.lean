module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ColimitPrismComparisonSection
public import SerrePositivity.InfinityCategories.HomotopyLimits.LocalColimitComparison

/-!
概要：局所同値な図式間の元の余極限余錐の prism の頂点辺が局所同値となることを証明する。
方針：join と直積の座標を保ち、元の両端と頂点の射を厳密に照合する。
規約：底 K は任意の単体集合。使われ方：HTT 5.5.4.5(2) の余極限閉性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の始点余錐から全図式の余錐の制限への、実際の指定比較辺。 -/
def colimitPrismComparisonEdge {K X : SSet.{u}}
    (G : (Δ[1] : SSet.{u}) ⊗ join K Δ[0] ⟶ X) :
    (sliceUnder (prismEndpoint 0 K ≫ colimitPrismDiagram G)).Edge
      (colimitPrismEndpoint G 0)
      ((sliceUnderRestrict (colimitPrismDiagram G) (prismEndpoint 0 K)).app
        (Opposite.op ⦋0⦌) (colimitPrismTotalCocone G)) where
  edge := SSet.yonedaEquiv (colimitPrismComparisonSection G)
  src_eq := by
    change (sliceUnder (prismEndpoint 0 K ≫ colimitPrismDiagram G)).δ 1
      (SSet.yonedaEquiv (colimitPrismComparisonSection G)) = colimitPrismEndpoint G 0
    rw [← stdSimplex.yonedaEquiv_δ_comp, colimitPrismComparisonSection_source,
      Equiv.apply_symm_apply]
  tgt_eq := by
    change (sliceUnder (prismEndpoint 0 K ≫ colimitPrismDiagram G)).δ 0
      (SSet.yonedaEquiv (colimitPrismComparisonSection G)) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, colimitPrismComparisonSection_target,
      Equiv.apply_symm_apply]
    rfl

/-- 比較辺の底への像は、元の余錐間の prism の頂点辺と厳密に一致する。 -/
lemma colimitPrismComparisonEdge_projection {K X : SSet.{u}}
    (G : (Δ[1] : SSet.{u}) ⊗ join K Δ[0] ⟶ X) :
    ((colimitPrismComparisonEdge G).map
      (sliceUnderProjection (prismEndpoint 0 K ≫ colimitPrismDiagram G))).edge =
      SSet.yonedaEquiv (prismVertexEvaluation G (SSet.yonedaEquiv (joinInr K Δ[0]))) := by
  change (sliceUnderProjection _).app (Opposite.op ⦋1⦌)
    (SSet.yonedaEquiv (colimitPrismComparisonSection G)) = _
  rw [← SSet.yonedaEquiv_comp]
  apply congrArg SSet.yonedaEquiv
  rw [← sliceUnderUncurry_projection, colimitPrismComparisonSection_uncurry,
    ← Category.assoc, colimitPrismComparisonMap_inr]
  rfl

/-- 両端が余極限で底の各辺が局所同値なら、元の prism の頂点辺も局所同値。 -/
lemma localEquivalences_colimitPrism_apex {K X : SSet.{u}} [Quasicategory X]
    (W : Set (X _⦋1⦌)) (G : (Δ[1] : SSet.{u}) ⊗ join K Δ[0] ⟶ X)
    (h₀ : IsColimitCone (colimitPrismEndpoint G 0))
    (h₁ : IsColimitCone (colimitPrismEndpoint G 1))
    (h : ∀ k : K _⦋0⦌,
      SSet.yonedaEquiv (prismVertexEvaluation (colimitPrismDiagram G) k) ∈ localEquivalences W) :
    SSet.yonedaEquiv (prismVertexEvaluation G (SSet.yonedaEquiv (joinInr K Δ[0]))) ∈
      localEquivalences W := by
  have he := localEquivalences_colimitPrism_source_comparison W (colimitPrismDiagram G)
    (colimitPrismTotalCocone G) (colimitPrismTotalCocone_isColimit G h₁)
    (colimitPrismEndpoint G 0) h₀ (colimitPrismComparisonEdge G) h
  rwa [colimitPrismComparisonEdge_projection] at he

end SerrePositivity.InfinityCategories.HomotopyLimits
