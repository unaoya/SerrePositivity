module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedEdges
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeHomotopy
/-!
概要：反転ホモトピーの実頂点辺と同じ閉 dg 射を回収する。
方針：同じ実 prism と反対比較を、一次単体と厳密切断で評価する。
規約：同じ全関手と閉射を保持する。使われ方：一般 RHom の標準写像空間判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial

/-- 反対 nerve 比較の逆は、同じ反対対象の頂点を元の頂点へ戻す。 -/
lemma dgNerveOppositeIso_inv_vertex (R : Type u) [CommRing R]
    (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] (x : C) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R C).inv.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (Opposite.op x)) =
      SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso_hom_vertex R C x]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (Iso.hom_inv_id (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R C)) _) _

/-- 反転ホモトピーの実頂点辺は、元の頂点辺の符号付き実反転。 -/
lemma dgNerveOppositeHomotopy_vertex_edge (R : Type u) [CommRing R]
    (C E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
    (F G : DGFunctor R C E) (H : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G)) (x : C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeHomotopy R C E F G H)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (Opposite.op x))).edge =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.opSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)).edge := by
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R E).hom.app (Opposite.op ⦋1⦌)
    ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite H).h.app (Opposite.op ⦋1⦌)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R C).inv.app (Opposite.op ⦋1⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R Cᵒᵖ).σ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (Opposite.op x))), _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) = _
  have hn := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R C).inv.naturality_apply
    (SimplexCategory.σ (0 : Fin 1)).op (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (Opposite.op x))
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R C).inv.app (Opposite.op ⦋1⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R Cᵒᵖ).σ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (Opposite.op x))) = _ at hn
  rw [hn, dgNerveOppositeIso_inv_vertex]
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R E).hom.app (Opposite.op ⦋1⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite H)
      (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))).edge = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanHomotopyOpposite_vertex_edge]
  rfl

/-- 閉 dg 射の実辺の反転は、同じ閉射の反対から作る実辺。 -/
lemma opSimplex_dgClosedEdge (R : Type u) [CommRing R]
    (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] {x y : _root_.SerrePositivity.DifferentialGraded.ClosedCategory R C} (f : x ⟶ y) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.opSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R C f).edge =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R Cᵒᵖ ((forgetEnrichmentOppositeEquivalence (Complex R) C).inverse.map
        f.op)).edge := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeEquiv.injective
  refine Sigma.ext ?_ ?_
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    apply Subtype.ext
    change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign 2 • _ = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign_two, one_smul]
    have hr : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse ({0, 1} : Finset (Fin 2)) = {0, 1} := by decide
    simp only [hr]
    rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
