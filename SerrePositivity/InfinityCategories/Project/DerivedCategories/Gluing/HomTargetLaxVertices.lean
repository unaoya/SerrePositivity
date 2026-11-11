module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetNerveLaxComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.LaxComparisonVertexImage
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ClosedArrowOfEdge
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed SSet DifferentialGraded
open KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M

lemma dgGluingHomTargetMap_vertex {U V : Type (max (u + 1) v)}
    [_root_.SerrePositivity.DifferentialGraded.DGCategory R U] [_root_.SerrePositivity.DifferentialGraded.DGCategory R V] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R U V) (x : U) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj x) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv (A := R) (D := V)).injective
  rfl

def dgGluingHomTargetClosedArrow (X : G) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E).Edge
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map p).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X.left))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map q).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X.right)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingEdgeEndpointTransport (dgGluingHomTargetMap_vertex R p X.left).symm
    (dgGluingHomTargetMap_vertex R q X.right).symm
    (Edge.ofTruncated (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E (dgHomGluingTargetMap R C D E p q X)))

lemma dgGluingHomTargetNerveLaxComparison_vertex (X : G) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNerveLaxComparison R C D E p q).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxFixedInputVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map q)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X.left) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X.right)
        (dgGluingHomTargetClosedArrow R C D E p q X) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackVertexEquiv _ _).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackVertexData _ _ _ =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackVertexData _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackVertexOfData _ _ _)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackVertexData_ofData]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackVertexData.ext
  · have h := ConcreteCategory.congr_hom (NatTrans.congr_app
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNerveLaxComparison_fst R C D E p q) (Opposite.op ⦋0⦌))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)
    exact h.trans (dgGluingHomTargetMap_vertex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M) X)
  · have h := ConcreteCategory.congr_hom (NatTrans.congr_app
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNerveLaxComparison_snd R C D E p q) (Opposite.op ⦋0⦌))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)
    exact h.trans (dgGluingHomTargetMap_vertex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M) X)
  · have h := ConcreteCategory.congr_hom (NatTrans.congr_app
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNerveLaxComparison_arrow R C D E p q) (Opposite.op ⦋0⦌))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map q)).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNerveLaxComparison R C D E p q).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationArrowFamily R C D E p q).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) at h
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge _ = _
    rw [h, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationArrowFamily, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCurryHomotopy_vertex_edge,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationHomotopy_vertex_edge]
    rfl

/-- 元二脚の任意の lax 頂点には、同じ二入力を持つ厳密な原像がある。 -/
lemma dgGluingHomTargetNerveLaxComparison_vertex_surjective :
    Function.Surjective
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNerveLaxComparison R C D E p q).app (Opposite.op ⦋0⦌)) := by
  intro z
  obtain ⟨a, b, e, he⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxFixedInputVertex_exists (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map q) z
  obtain ⟨c, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv (A := R) (D := C)).symm.surjective a
  obtain ⟨d, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv (A := R) (D := D)).symm.surjective b
  have hp : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map p).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex c) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (p.obj c) := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv (A := R) (D := E)).injective
    rfl
  have hq : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map q).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex d) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (q.obj d) := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv (A := R) (D := E)).injective
    rfl
  obtain ⟨f, hf⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedArrowOfEdge R E (p.obj c) (q.obj d)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingEdgeEndpointTransport hp hq e)
  let X : G := ⟨c, d, _root_.SerrePositivity.DifferentialGraded.closedHomEquiv R E _ _ f⟩
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X, ?_⟩
  rw [dgGluingHomTargetNerveLaxComparison_vertex, ← he]
  congr 1
  apply Edge.ext
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E ((closedHomEquiv R E _ _).symm
    (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R E _ _ f))).edge = e.edge
  rw [Equiv.symm_apply_apply]
  exact congrArg Edge.edge hf

/-- 同じ比較は追加の生成・完備性仮定なしに本質的全射である。 -/
lemma dgGluingHomTargetNerveLaxComparison_isEssentiallySurjective :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNerveLaxComparison R C D E p q) := by
  intro z
  obtain ⟨x, hx⟩ := dgGluingHomTargetNerveLaxComparison_vertex_surjective R C D E p q z
  exact ⟨x, hx ▸ ⟨Iso.refl _⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
