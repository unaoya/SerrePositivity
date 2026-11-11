module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniversalCounitInterval
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniversalRightAdjointValue
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CounitMappingAdjunction
/-!
概要：同じ実普遍余単位と厳密切断の全関手を、三角式付きの実 ∞ 随伴へ昇格する。
方針：同じ実辺の回収と標準比較の反転を、全パラメータの随伴判定へ渡す。
規約：元の全関手と厳密切断を保持する。使われ方：一般 kernel の実 RHom 随伴。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial

/-- 厳密切断から作る同じ右随伴候補の頂点値。 -/
lemma dgUniversalRightAdjointCandidate_vertex
    (R : Type u) [CommRing R] (C E : Type (max (u + 1) v))
    [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
    (h : ∀ y : E, Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniversalCounit R C E F y)) (y : E) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalRightAdjointCandidate R C E F h).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalRightAdjointObject R C E F h y).label.universal.source := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
  rfl

/-- 同じ厳密切断の実余単位による、全区間写像空間の標準比較は同値。 -/
lemma dgUniversalRightAdjointCounit_interval_equivalence
    (R : Type u) [CommRing R] (C E : Type (max (u + 1) v))
    [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
    (h : ∀ y : E, Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniversalCounit R C E F y))
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) _⦋0⦌) (y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) x
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalRightAdjointCandidate R C E F h).app (Opposite.op ⦋0⦌) y) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPostcompose ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F).app (Opposite.op ⦋0⦌) x)
          (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalRightAdjointCounitHomotopy R C E F h) y).toTruncated)) := by
  obtain ⟨x, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective x
  obtain ⟨y, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective y
  let z := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalRightAdjointObject R C E F h y
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.intervalFunctorPostcompose_equivalence_of_endpoint (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalRightAdjointCandidate R C E F h).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex z.label.universal.source)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalRightAdjointCounitHomotopy R C E F h)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))
    (SSet.Edge.ofTruncated (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E z.label.universal.counit))
    (dgUniversalRightAdjointCandidate_vertex R C E F h y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex F x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex F z.label.universal.source)
    (congrArg (fun t : E ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) t)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalRightAdjointObject_target R C E F h y).symm)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalRightAdjointCounitHomotopy_vertex_edge R C E F h y)
    (z.label.universal.nativeIntervalMap_isSimplicialHomotopyEquivalence x)

/-- 同じ実 dg 関手と厳密切断の右随伴候補による ∞ 随伴。 -/
def dgUniversalRightAdjunction
    (R : Type u) [CommRing R] (C E : Type (max (u + 1) v))
    [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
    (h : ∀ y : E, Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniversalCounit R C E F y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalRightAdjointCandidate R C E F h) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.qcatAdjunctionOfCounitIntervalCondition (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalRightAdjointCounitHomotopy R C E F h)
    (dgUniversalRightAdjointCounit_interval_equivalence R C E F h)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
