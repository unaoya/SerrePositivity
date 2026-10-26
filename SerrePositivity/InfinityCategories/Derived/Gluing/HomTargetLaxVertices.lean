module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetNerveLaxComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxComparisonVertexImage
public import SerrePositivity.InfinityCategories.Derived.Gluing.ClosedArrowOfEdge
/-!
概要：元終域の lax 比較は全頂点を元二脚と元閉比較射のまま回収する。
方針：実 prism の頂点辺を照合し、任意の nerve 辺を閉零射へ厳密に戻す。
規約：本質的全射性より強い頂点の全射性。Hom 比較の同値性は別工程。
使われ方：元二脚・恒等二脚の全比較の対象側。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed SSet DifferentialGraded DGNerve
open KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "G" => DGGluingObject R C D M

lemma dgGluingHomTargetMap_vertex {U V : Type (max (u + 1) v)}
    [DGCategory R U] [DGCategory R V] (F : DGFunctor R U V) (x : U) :
    (dgNerve.map F).app (Opposite.op ⦋0⦌) (Simplex.vertex x) =
      Simplex.vertex (F.obj x) := by
  apply (Simplex.vertexEquiv (A := R) (D := V)).injective
  rfl

def dgGluingHomTargetClosedArrow (X : G) :
    (dgNerve R E).Edge
      ((dgNerve.map p).app (Opposite.op ⦋0⦌) (Simplex.vertex X.left))
      ((dgNerve.map q).app (Opposite.op ⦋0⦌) (Simplex.vertex X.right)) :=
  dgGluingEdgeEndpointTransport (dgGluingHomTargetMap_vertex R p X.left).symm
    (dgGluingHomTargetMap_vertex R q X.right).symm
    (Edge.ofTruncated (X := dgNerve R E)
      (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q X)))

lemma dgGluingHomTargetNerveLaxComparison_vertex (X : G) :
    (dgGluingHomTargetNerveLaxComparison R C D E p q).app (Opposite.op ⦋0⦌)
        (Simplex.vertex X) =
      dgGluingLaxFixedInputVertex (dgNerve.map p) (dgNerve.map q)
        (Simplex.vertex X.left) (Simplex.vertex X.right)
        (dgGluingHomTargetClosedArrow R C D E p q X) := by
  apply (F2.laxPullbackVertexEquiv _ _).injective
  change F2.laxPullbackVertexData _ _ _ =
    F2.laxPullbackVertexData _ _ (F2.laxPullbackVertexOfData _ _ _)
  rw [F2.laxPullbackVertexData_ofData]
  apply F2.LaxPullbackVertexData.ext
  · have h := ConcreteCategory.congr_hom (NatTrans.congr_app
      (dgGluingHomTargetNerveLaxComparison_fst R C D E p q) (Opposite.op ⦋0⦌))
        (Simplex.vertex X)
    exact h.trans (dgGluingHomTargetMap_vertex R (dgGluingLeft R C D M) X)
  · have h := ConcreteCategory.congr_hom (NatTrans.congr_app
      (dgGluingHomTargetNerveLaxComparison_snd R C D E p q) (Opposite.op ⦋0⦌))
        (Simplex.vertex X)
    exact h.trans (dgGluingHomTargetMap_vertex R (dgGluingRight R C D M) X)
  · have h := ConcreteCategory.congr_hom (NatTrans.congr_app
      (dgGluingHomTargetNerveLaxComparison_arrow R C D E p q) (Opposite.op ⦋0⦌))
        (Simplex.vertex X)
    change (F2.laxPullbackArrow (dgNerve.map p) (dgNerve.map q)).app (Opposite.op ⦋0⦌)
      ((dgGluingHomTargetNerveLaxComparison R C D E p q).app (Opposite.op ⦋0⦌)
        (Simplex.vertex X)) =
      (dgGluingHomTargetAugmentationArrowFamily R C D E p q).app (Opposite.op ⦋0⦌)
        (Simplex.vertex X) at h
    change intervalFunctorVertexEdge _ = _
    rw [h, dgGluingHomTargetAugmentationArrowFamily, dgGluingCurryHomotopy_vertex_edge,
      dgGluingHomTargetAugmentationHomotopy_vertex_edge]
    rfl

/-- 元二脚の任意の lax 頂点には、同じ二入力を持つ厳密な原像がある。 -/
lemma dgGluingHomTargetNerveLaxComparison_vertex_surjective :
    Function.Surjective
      ((dgGluingHomTargetNerveLaxComparison R C D E p q).app (Opposite.op ⦋0⦌)) := by
  intro z
  obtain ⟨a, b, e, he⟩ := dgGluingLaxFixedInputVertex_exists (dgNerve.map p) (dgNerve.map q) z
  obtain ⟨c, rfl⟩ := (Simplex.vertexEquiv (A := R) (D := C)).symm.surjective a
  obtain ⟨d, rfl⟩ := (Simplex.vertexEquiv (A := R) (D := D)).symm.surjective b
  have hp : (dgNerve.map p).app (Opposite.op ⦋0⦌) (Simplex.vertex c) =
      Simplex.vertex (p.obj c) := by
    apply (Simplex.vertexEquiv (A := R) (D := E)).injective
    rfl
  have hq : (dgNerve.map q).app (Opposite.op ⦋0⦌) (Simplex.vertex d) =
      Simplex.vertex (q.obj d) := by
    apply (Simplex.vertexEquiv (A := R) (D := E)).injective
    rfl
  obtain ⟨f, hf⟩ := dgGluingClosedArrowOfEdge R E (p.obj c) (q.obj d)
    (dgGluingEdgeEndpointTransport hp hq e)
  let X : G := ⟨c, d, closedHomEquiv R E _ _ f⟩
  refine ⟨Simplex.vertex X, ?_⟩
  rw [dgGluingHomTargetNerveLaxComparison_vertex, ← he]
  congr 1
  apply Edge.ext
  change (dgClosedEdge R E ((closedHomEquiv R E _ _).symm
    (closedHomEquiv R E _ _ f))).edge = e.edge
  rw [Equiv.symm_apply_apply]
  exact congrArg Edge.edge hf

/-- 同じ比較は追加の生成・完備性仮定なしに本質的全射である。 -/
lemma dgGluingHomTargetNerveLaxComparison_isEssentiallySurjective :
    IsEssentiallySurjective (dgGluingHomTargetNerveLaxComparison R C D E p q) := by
  intro z
  obtain ⟨x, hx⟩ := dgGluingHomTargetNerveLaxComparison_vertex_surjective R C D E p q z
  exact ⟨x, hx ▸ ⟨Iso.refl _⟩⟩

end SerrePositivity.InfinityCategories
