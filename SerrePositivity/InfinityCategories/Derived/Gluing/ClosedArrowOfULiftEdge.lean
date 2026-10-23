module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ClosedArrowOfEdge
public import SerrePositivity.InfinityCategories.F1.Universe.InvertibleEdge

/-! 持ち上げた dg nerve の実辺も、元の同じ閉射の持ち上げへ厳密に戻る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial

lemma dgGluingClosedArrowOfULiftEdge (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
    (x y : D) (b : ((SSet.uliftFunctor.{w, max u v}).obj (dgNerve R D)).Edge
      (ULift.up (Simplex.vertex x)) (ULift.up (Simplex.vertex y))) :
    ∃ a : ForgetEnrichment.of (Complex R) x ⟶ ForgetEnrichment.of (Complex R) y,
      Edge.ofTruncated (uliftTruncatedEdge.{max u v, w}
        (X := dgNerve R D) (dgClosedEdge R D a)) = b := by
  let c : (dgNerve R D).Edge (Simplex.vertex x) (Simplex.vertex y) :=
    ⟨b.edge.down, congrArg ULift.down b.src_eq, congrArg ULift.down b.tgt_eq⟩
  obtain ⟨a, ha⟩ := dgGluingClosedArrowOfEdge R D x y c
  refine ⟨a, ?_⟩
  apply Edge.ext
  apply ULift.ext
  exact congrArg Edge.edge ha

end SerrePositivity.InfinityCategories
