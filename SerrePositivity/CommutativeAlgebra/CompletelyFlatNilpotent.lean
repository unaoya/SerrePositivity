module
public import SerrePositivity.HomologicalAlgebra.NilpotentModuleFiltration
public import SerrePositivity.HomologicalAlgebra.TorDimensionShift
public import SerrePositivity.CommutativeAlgebra.CompletelyFlatCriterion

/-! # Complete flatness for arbitrary nilpotent ideals is ordinary flatness -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]

/-- Extend complete flatness to all modules annihilated by a power of any ideal. -/
lemma torModule_subsingleton_of_completelyFlat_idealPowerTorsion
    (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] (hM : IsCompletelyFlat I M)
    (n : ℕ) (N : ModuleCat.{u} R) (hN : ∀ r ∈ I ^ n, ∀ x : N, r • x = 0)
    (i : ℕ) (hi : 0 < i) : Subsingleton (TorModule R i M N) := by
  let P : ModuleCat.{u} R → Prop := fun N ↦ Subsingleton (TorModule R i M N)
  apply moduleProperty_of_idealPower_annihilated I P ?_ ?_ n N hN
  · intro N hN
    exact (isConcentratedInDegreeZero_derivedTensor_iff M N).mp (hM N hN) i hi
  · intro S hS h₁ h₃
    exact torModule_subsingleton_of_exact M S.f.hom S.g.hom
      ((ModuleCat.mono_iff_injective _).mp hS.mono_f)
      ((ModuleCat.epi_iff_surjective _).mp hS.epi_g)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact) i h₁ h₃

/-- Complete flatness for a nilpotent ideal tests all modules and gives ordinary flatness. -/
lemma flat_of_completelyFlat_nilpotent (I : Ideal R) (hNil : ∃ n : ℕ, I ^ n = ⊥)
    (M : Type u) [AddCommGroup M] [Module R M] (hM : IsCompletelyFlat I M) :
    Module.Flat R M := by
  obtain ⟨n, hn⟩ := hNil
  have ht (N : Type u) [AddCommGroup N] [Module R N] :
      Subsingleton (TorModule R 1 M N) := by
    apply torModule_subsingleton_of_completelyFlat_idealPowerTorsion I M hM n
      (ModuleCat.of R N) ?_ 1 (by omega)
    intro r hr x
    rw [hn, Ideal.mem_bot] at hr
    rw [hr, zero_smul]
  apply Module.Flat.iff_lTensor_preserves_injective_linearMap.mpr
  intro N N' _ _ _ _ f hf
  exact lTensor_injective_of_torModule_one M f f.range.mkQ hf f.range.mkQ_surjective
    f.exact_map_mkQ_range (ht (N' ⧸ f.range))

/-- Over a nilpotent ideal, the existing complete flatness predicate is equivalent to flatness. -/
lemma isCompletelyFlat_nilpotent_iff_flat (I : Ideal R) (hNil : ∃ n : ℕ, I ^ n = ⊥)
    (M : Type u) [AddCommGroup M] [Module R M] :
    IsCompletelyFlat I M ↔ Module.Flat R M := by
  refine ⟨flat_of_completelyFlat_nilpotent I hNil M, ?_⟩
  intro hFlat
  let hF := hFlat
  intro N _ _ hN
  apply (isConcentratedInDegreeZero_derivedTensor_iff M N).mpr
  intro i hi
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  exact torModule_subsingleton_of_flat M N j

/-- The discrete case of G10: an acyclic flat residue extension over a nilpotent ideal lifts. -/
lemma flat_of_acyclic_flat_nilpotent_reduction (I : Ideal R) (hNil : ∃ n : ℕ, I ^ n = ⊥)
    (M : Type u) [AddCommGroup M] [Module R M]
    (hTor : scalarExtensionTorVanishing (Ideal.Quotient.mk I) (ModuleCat.of R M))
    (hFlat : Module.Flat (R ⧸ I)
      ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj (ModuleCat.of R M))) :
    Module.Flat R M :=
  flat_of_completelyFlat_nilpotent I hNil M
    (isCompletelyFlat_of_acyclic_flat_reduction I M hTor hFlat)

end SerrePositivity
