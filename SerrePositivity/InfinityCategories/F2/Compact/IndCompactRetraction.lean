module

public import SerrePositivity.InfinityCategories.F2.Compact.FilteredRetraction
public import SerrePositivity.InfinityCategories.F2.Ind.IndVertexDensity

/-!
概要：Indκ 内の元の任意の κ-compact 頂点は、元の Yoneda 像の retract。
方針：元の頂点を厳密に持つ小さい κ-filtered 密度余錐へ、恒等点の因子化を適用する。
規約：元の指定 Ind 頂点・元の圏の対象・同じ Yoneda を保持。κ は正則。
使われ方：compact Ind と Idem の実比較の本質全射性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 元の任意の compact Ind 頂点は、同じ元の Ind 内で元の Yoneda 像の retract。 -/
lemma indCompact_retract_yoneda (κ : Cardinal.{u}) [Fact κ.IsRegular]
    {C : SSet.{u}} [Quasicategory C] (x : Ind.IndInfinity κ C _⦋0⦌)
    (hx : IsKappaCompact.{u, u + 1} κ x) :
    ∃ a : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf x
      ((Ind.indYoneda κ C).app (Opposite.op ⦋0⦌) (ULift.up a)) := by
  have : IsKappaFiltered κ (smallRightUnstraightening (Ind.indVertexPresheaf κ x)) :=
    Ind.indVertexElements_isKappaFiltered κ x
  have h : IsKappaCompact.{u, u + 1} κ (Ind.indVertexDensityCocone κ x).vertex :=
    (Ind.indVertexDensityCocone_vertex κ x).symm ▸ hx
  obtain ⟨i, hi⟩ := IsKappaCompact.retract_of_colimit
    (Ind.indDensityDiagram κ (Ind.indVertexPresheaf κ x))
    (Ind.indVertexDensityCocone κ x) (Ind.indVertexDensityCocone_isColimit κ x) h
  refine ⟨(smallRightUnstraighteningProjection (Ind.indVertexPresheaf κ x)).app
    (Opposite.op ⦋0⦌) i, ?_⟩
  have hv : ((SSet.uliftFunctor.{u + 1, u}).map
      (smallRightUnstraighteningProjection (Ind.indVertexPresheaf κ x))).app
      (Opposite.op ⦋0⦌) (ULift.up i) = ULift.up
        ((smallRightUnstraighteningProjection (Ind.indVertexPresheaf κ x)).app
          (Opposite.op ⦋0⦌) i) := by rfl
  simp only [Ind.indVertexDensityCocone_vertex, Ind.indDensityDiagram,
    SSet.comp_app, types_comp_apply] at hi
  rw [hv] at hi
  exact hi

end SerrePositivity.InfinityCategories.F2.Compact
