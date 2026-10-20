module
public import SerrePositivity.InfinityCategories.Derived.DGProjectiveModules
public import SerrePositivity.InfinityCategories.Stable.EquivalenceStability
/-!
概要：半自由加群と射影的加群の実 dg nerve の比較同値と半自由模型の安定性。
方針：実半自由分解の準同型を射影性で反転し、全包含で同型を持ち上げる。
規約：半自由性のホモトピー同型に関する閉性を仮定しない。使われ方：β5 の D(A)。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 射影的加群は実半自由分解と、射影的加群の nerve 内で同型。 -/
lemma dgSemifreeToProjectiveNerve_isEssentiallySurjective :
    IsEssentiallySurjective (dgNerve.map (dgSemifreeToProjective R D)) := by
  intro b
  obtain ⟨N, rfl⟩ := Simplex.vertexEquiv.symm.surjective b
  obtain ⟨P, π, _, hπ⟩ := dgSemifreeModule_resolution_exists R D N.val
  let g := dgNerve.map (dgSemifreeToProjective R D)
  let i := dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
    (dgModuleProjectiveProperty R D))
  have h₀ : i.app (Opposite.op ⦋0⦌) (g.app (Opposite.op ⦋0⦌) (Simplex.vertex P)) =
      Simplex.vertex P.val := by
    rw [dgFunctorNerve_vertex, dgFunctorNerve_vertex]
    rfl
  have h₁ : i.app (Opposite.op ⦋0⦌) (Simplex.vertex N) = Simplex.vertex N.val :=
    dgFunctorNerve_vertex _ N
  have := dgModuleEdge_isIso_of_homotopy R D π
    (moduleHomotopicallyProjective_quasiIso_isIso_homotopy R D
      (dgSemifreeModule_isProjective R D P) N.property π hπ)
  have : IsInvertibleEdge (X := dgModuleNerve R D) (dgModuleEdge R D π).toTruncated :=
    (edgeToPathHomotopyCategory _).map_isIso
      (Truncated.HomotopyCategory₂.homMk (dgModuleEdge R D π).toTruncated)
  let J : VertexIso (i.app (Opposite.op ⦋0⦌)
      (g.app (Opposite.op ⦋0⦌) (Simplex.vertex P))) (i.app (Opposite.op ⦋0⦌) (Simplex.vertex N)) :=
    eqToIso (congrArg SSet.HomotopyCategory.mk h₀) ≪≫
      asIso (Truncated.HomotopyCategory.homMk (dgModuleEdge R D π).toTruncated) ≪≫
        eqToIso (congrArg SSet.HomotopyCategory.mk h₁.symm)
  let ff := (dgFullSubcategoryInclusionNerve_isFullyFaithful R (RightModule R D)
    (dgModuleProjectiveProperty R D)).toHoFullyFaithful
  exact ⟨Simplex.vertex P, ⟨ff.preimageIso J⟩⟩
/-- 全 Hom end を保つ半自由・射影的模型の比較は実 ∞ 圏同値。 -/
theorem dgSemifreeToProjectiveNerve_isQCatEquivalence :
    IsQCatEquivalence (dgNerve.map (dgSemifreeToProjective R D)) :=
  isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (dgSemifreeToProjectiveNerve_isFullyFaithful R D)
    (dgSemifreeToProjectiveNerve_isEssentiallySurjective R D)
/-- 半自由 dg 加群による導来 ∞ 圏の模型は安定。 -/
theorem dgModuleDerivedInfinityCategory_isStable : IsStable (dgModuleDerivedInfinityCategory R D) :=
  (dgSemifreeToProjectiveNerve_isQCatEquivalence R D).isStable_iff.mpr
    (dgProjectiveModuleNerve_isStable R D)
end SerrePositivity.InfinityCategories
