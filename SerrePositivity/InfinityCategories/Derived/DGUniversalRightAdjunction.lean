module
public import SerrePositivity.InfinityCategories.Derived.DGUniversalCounitInterval
public import SerrePositivity.InfinityCategories.Derived.DGUniversalRightAdjointValue
public import SerrePositivity.InfinityCategories.Stable.CounitMappingAdjunction
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial

/-- 厳密切断から作る同じ右随伴候補の頂点値。 -/
lemma dgUniversalRightAdjointCandidate_vertex
    (R : Type u) [CommRing R] (C E : Type (max (u + 1) v))
    [DGCategory R C] [DGCategory R E] (F : DGFunctor R C E)
    (h : ∀ y : E, Nonempty (DGUniversalCounit R C E F y)) (y : E) :
    (dgUniversalRightAdjointCandidate R C E F h).app (Opposite.op ⦋0⦌) (Simplex.vertex y) =
      Simplex.vertex (dgUniversalRightAdjointObject R C E F h y).label.universal.source := by
  apply Simplex.vertexEquiv.injective
  rfl

/-- 同じ厳密切断の実余単位による、全区間写像空間の標準比較は同値。 -/
lemma dgUniversalRightAdjointCounit_interval_equivalence
    (R : Type u) [CommRing R] (C E : Type (max (u + 1) v))
    [DGCategory R C] [DGCategory R E] (F : DGFunctor R C E)
    (h : ∀ y : E, Nonempty (DGUniversalCounit R C E F y))
    (x : (dgNerve R C) _⦋0⦌) (y : (dgNerve R E) _⦋0⦌) :
    IsSimplicialHomotopyEquivalence
      (intervalFunctorMap (dgNerve.map F) x
        ((dgUniversalRightAdjointCandidate R C E F h).app (Opposite.op ⦋0⦌) y) ≫
        intervalPostcompose ((dgNerve.map F).app (Opposite.op ⦋0⦌) x)
          (Truncated.HomotopyCategory.homMk (simplicialHomotopyVertexEdge
            (dgUniversalRightAdjointCounitHomotopy R C E F h) y).toTruncated)) := by
  obtain ⟨x, rfl⟩ := Simplex.vertexEquiv.symm.surjective x
  obtain ⟨y, rfl⟩ := Simplex.vertexEquiv.symm.surjective y
  let z := dgUniversalRightAdjointObject R C E F h y
  exact intervalFunctorPostcompose_equivalence_of_endpoint (dgNerve.map F)
    (Simplex.vertex x)
    ((dgUniversalRightAdjointCandidate R C E F h).app (Opposite.op ⦋0⦌) (Simplex.vertex y))
    (Simplex.vertex z.label.universal.source)
    (simplicialHomotopyVertexEdge (dgUniversalRightAdjointCounitHomotopy R C E F h)
      (Simplex.vertex y))
    (SSet.Edge.ofTruncated (X := dgNerve R E) (dgClosedEdge R E z.label.universal.counit))
    (dgUniversalRightAdjointCandidate_vertex R C E F h y)
    (dgFunctorNerve_vertex F x) (dgFunctorNerve_vertex F z.label.universal.source)
    (congrArg (fun t : E ↦ Simplex.vertex (A := R) t)
      (dgUniversalRightAdjointObject_target R C E F h y).symm)
    (dgUniversalRightAdjointCounitHomotopy_vertex_edge R C E F h y)
    (z.label.universal.nativeIntervalMap_isSimplicialHomotopyEquivalence x)

/-- 同じ実 dg 関手と厳密切断の右随伴候補による ∞ 随伴。 -/
def dgUniversalRightAdjunction
    (R : Type u) [CommRing R] (C E : Type (max (u + 1) v))
    [DGCategory R C] [DGCategory R E] (F : DGFunctor R C E)
    (h : ∀ y : E, Nonempty (DGUniversalCounit R C E F y)) :
    QCatAdjunction (dgNerve.map F) (dgUniversalRightAdjointCandidate R C E F h) :=
  qcatAdjunctionOfCounitIntervalCondition (dgUniversalRightAdjointCounitHomotopy R C E F h)
    (dgUniversalRightAdjointCounit_interval_equivalence R C E F h)
end SerrePositivity.InfinityCategories
