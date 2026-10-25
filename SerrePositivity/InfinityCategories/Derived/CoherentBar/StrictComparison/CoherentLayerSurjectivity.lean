module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerDifferential

/-!
概要：各単体次元層の元は実 bar の同じ段階から持ち上がる。
方針：層の実余積の有限表示を同じ正規化包含へ送り、包含と射影の分裂を使う。
規約：全整数次数の実写像を用いる。
使われ方：段階商と内部複体を同定する際の次数ごとの全射性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarLayerInclusion_mem_filtration (x : D) (q : ℤ) (n : ℕ)
    (z : (moduleDegreeEvaluation R D x q).obj (dgCoherentBarLayerGraded R D G n)) :
    (moduleDegreeEvaluation R D x q).map (dgCoherentBarLayerInclusion R D G n) z ∈
      dgCoherentBarNormalizedDegreeFiltration R D G x q n := by
  classical
  obtain ⟨t, a, ha⟩ := moduleCofan_element_rep R
    (fun s => (moduleDegreeEvaluation R D x q).obj (dgCoherentBarLayerFamily R D G n s))
    _ (moduleCoproductDegreeIsColimit R D (dgCoherentBarLayerFamily R D G n) x q) z
  rw [← ha, map_sum]
  apply Submodule.sum_mem
  intro s hs
  change (moduleDegreeEvaluation R D x q).map (dgCoherentBarLayerInclusion R D G n)
    ((moduleDegreeEvaluation R D x q).map
      (Sigma.ι (dgCoherentBarLayerFamily R D G n) s) (a s)) ∈ _
  erw [← ModuleCat.comp_apply, ← CategoryTheory.Functor.map_comp, dgCoherentBarLayerInclusion_ι]
  exact dgCoherentBarNormalizedDegreeFiltration_inclusion R D G x q n s.val s.property.le (a s)

lemma dgCoherentBarStageToLayer_surjective (x : D) (q : ℤ) (n : ℕ) :
    Function.Surjective ((dgCoherentBarStageToLayer R D G x n).f q) := by
  intro z
  let a := (moduleDegreeEvaluation R D x q).map (dgCoherentBarLayerInclusion R D G n) z
  have ha := dgCoherentBarLayerInclusion_mem_filtration R D G x q n z
  refine ⟨⟨a, ha⟩, ?_⟩
  change (moduleDegreeEvaluation R D x q).map (dgCoherentBarLayerProjection R D G n)
    ((moduleDegreeEvaluation R D x q).map (dgCoherentBarLayerInclusion R D G n) z) = z
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, dgCoherentBarLayerInclusion_projection,
    CategoryTheory.Functor.map_id, ModuleCat.id_apply]

end SerrePositivity.InfinityCategories
