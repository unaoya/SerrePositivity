module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGFullKernelEssentialImage
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGStableSubcategory
/-!
概要：完全関手の零対象核で定まる充満 dg 部分圏は実際に安定で、包含は完全。
方針：既存の実安定閉包の零化判定へ零・fiber・cofiber の生成を渡す。
規約：対象条件は零対象核との同値だけを仮定し、商の局所化を使わない。
使われ方：D-16 の新 thick 核を Sp の安定圏と完全包含に束ねる前の入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
  [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)] (P : D → Prop)
  {Y : SSet.{max u v}} [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y]
  (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F]
  (hP : ∀ x, P x ↔ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)))
include hP

lemma dgFullKernelProperty_isStable : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStableObjectProperty R D P := by
  let K : Set ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) _⦋0⦌) := {x | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (F.app (Opposite.op ⦋0⦌) x)}
  have hk : ∀ x ∈ K, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (F.app (Opposite.op ⦋0⦌) x) := fun _ h => h
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    apply (hP _).mpr
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_vertex_obj]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := F) z hz
  · intro t ht h₀ h₁
    have hz₀ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 0 0 ∈ K := by
      simpa only [K, Set.mem_setOf_eq, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_vertex_obj] using (hP _).mp h₀
    have hz₁ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 0 ∈ K := by
      simpa only [K, Set.mem_setOf_eq, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_vertex_obj] using (hP _).mp h₁
    apply (hP _).mpr
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_vertex_obj]
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kills_stableVertexClosure F K hk
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_cofiber t ht (.of_mem hz₀) (.of_mem hz₁))
  · intro t ht h₁ h₂
    have hz₁ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 0 ∈ K := by
      simpa only [K, Set.mem_setOf_eq, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_vertex_obj] using (hP _).mp h₁
    have hz₂ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 1 ∈ K := by
      simpa only [K, Set.mem_setOf_eq, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_vertex_obj] using (hP _).mp h₂
    apply (hP _).mpr
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_vertex_obj]
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kills_stableVertexClosure F K hk
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_fiber t ht (.of_mem hz₁) (.of_mem hz₂))

lemma dgFullKernelNerve_isStable : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFullSubcategory D P)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableSubcategory_isStable R D P (dgFullKernelProperty_isStable R D P F hP)

lemma dgFullKernelInclusion_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R D P)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableSubcategoryInclusion_isExactFunctor R D P (dgFullKernelProperty_isStable R D P F hP)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
