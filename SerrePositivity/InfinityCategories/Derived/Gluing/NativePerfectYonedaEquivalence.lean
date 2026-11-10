module
public import SerrePositivity.InfinityCategories.Derived.DGPerfectYonedaIdempotentCompletion
public import SerrePositivity.InfinityCategories.F2.Idempotent.CompleteImageRetracts
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulEquivalence
/-!
概要：coherent 冪等完備な小前三角 dg 圏の元 native perfect Yoneda は全同値。
方針：元 perfect 頂点の retract 表示を、元の充満忠実 Yoneda 像の中で分裂する。
規約：全 Perf の Small 性や固定 S の値を使用しない。使われ方：恒等 cone 比較の終域同値。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
open F2.Idempotent
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type (u + 1)) [DGCategory R C] [Small.{u} C]
  [IsDGPretriangulated R C]

lemma dgGluingNativePerfectYoneda_fullyFaithful :
    IsFullyFaithful (dgNerve.map (dgPerfectYoneda R C)) := by
  apply dgNerve_map_isFullyFaithful_of_homIso
  intro x y
  change IsIso (dgYonedaIso (D := C) R x (representable R y)).inv
  infer_instance

lemma dgGluingNativePerfectYoneda_equivalence (hC : IsIdempotentComplete (dgNerve R C)) :
    IsQCatEquivalence (dgNerve.map (dgPerfectYoneda R C)) := by
  let Y := dgNerve.map (dgPerfectYoneda R C)
  have hf : IsFullyFaithful Y := dgGluingNativePerfectYoneda_fullyFaithful R C
  have he : IsEssentiallySurjective Y := by
    intro z
    obtain ⟨M, rfl⟩ := (Simplex.vertexEquiv (A := R) (D := PerfectDGModule R C)).symm.surjective z
    obtain ⟨x, ⟨r⟩⟩ := dgPerfectVertex_retract_yoneda R C M
    have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction (Simplex.vertex M) (Y.app (Opposite.op ⦋0⦌) (Simplex.vertex x)) := by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction (Simplex.vertex M)
        ((dgNerve.map (dgPerfectYoneda R C)).app (Opposite.op ⦋0⦌) (Simplex.vertex x))
      rw [dgFunctorNerve_vertex]
      exact r
    obtain ⟨x', ⟨e⟩⟩ := hC.retract_iso_in_image Y hf (Simplex.vertex x) (Simplex.vertex M) hr
    exact ⟨x', ⟨e.symm⟩⟩
  exact isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective Y hf he

def dgGluingNativePerfectYonedaEquivalence (hC : IsIdempotentComplete (dgNerve R C)) :
    QCatEquivalence (dgNerve R C) (dgNerve R (PerfectDGModule R C)) :=
  (dgGluingNativePerfectYoneda_equivalence R C hC).choose

end SerrePositivity.InfinityCategories
