module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGUniversalCommaCounitComponent
/-!
概要：厳密切断の実普遍余単位と右随伴候補の各値を回収する。
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

/-- 同じ厳密切断が選ぶ普遍余単位の実対象。 -/
def dgUniversalRightAdjointObject
    (R : Type u) [CommRing R] (C E : Type (max (u + 1) v))
    [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
    (h : ∀ y : E, Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniversalCounit R C E F y)) (y : E) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniversalComma R C E F := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaNerveEquivalence R C E F h).inv.app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))

/-- 厳密切断が選ぶ普遍余単位の標的は、元の同じ対象。 -/
lemma dgUniversalRightAdjointObject_target
    (R : Type u) [CommRing R] (C E : Type (max (u + 1) v))
    [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
    (h : ∀ y : E, Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniversalCounit R C E F y)) (y : E) :
    (dgUniversalRightAdjointObject R C E F h y).label.target = y := by
  have he := congrArg (fun f ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv
    (f.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaNerveEquivalence_inv_hom R C E F h)
  exact he

/-- 右随伴候補の実余単位の頂点辺は、同じ厳密切断で選ぶ閉射。 -/
lemma dgUniversalRightAdjointCounitHomotopy_vertex_edge
    (R : Type u) [CommRing R] (C E : Type (max (u + 1) v))
    [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
    (h : ∀ y : E, Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniversalCounit R C E F y)) (y : E) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalRightAdjointCounitHomotopy R C E F h)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)).edge =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E
        (dgUniversalRightAdjointObject R C E F h y).label.universal.counit).edge := by
  let s := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaNerveEquivalence R C E F h).inv
  have hn := s.naturality_apply (SimplexCategory.σ (0 : Fin 1)).op (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaCounitHomotopy R C E F).h.app (Opposite.op ⦋1⦌)
    (s.app (Opposite.op ⦋1⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E).σ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _
  change s.app (Opposite.op ⦋1⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E).σ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) = _ at hn
  rw [hn]
  have hv : s.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (dgUniversalRightAdjointObject R C E F h y) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
    rfl
  rw [hv]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaCounitHomotopy_vertex_edge R C E F _
end SerrePositivity.InfinityCategories.Project.DerivedCategories
