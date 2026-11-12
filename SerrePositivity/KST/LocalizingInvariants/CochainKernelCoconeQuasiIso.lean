module

public import SerrePositivity.KST.LocalizingInvariants.CochainKernelCoconeComparison
public import SerrePositivity.KST.LocalizingInvariants.CochainMappingCoconeMapSurjective
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation

/-!
概要：次数全射な複体射の kernel と cocone の標準比較は準同型である。
方針：恒等射の非輪な cocone を右項とする実短完全列の長完全列を使う。
規約：非有界複体に適用。使われ方：通常 pullback と乗法的経路模型の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CochainComplex HomComplex HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] {K L : Complex R} (d : K ⟶ L)

lemma cochainCoconeToIdentity_epi [Epi d] : Epi (cochainCoconeToIdentity d) := by
  apply epi_of_epi_f
  intro n
  apply (ModuleCat.epi_iff_surjective _).2
  apply cochainMappingCoconeMap_surjective d (𝟙 L) d (𝟙 L) (by simp) n
  · exact (ModuleCat.epi_iff_surjective _).1 inferInstance
  · intro x
    exact ⟨x, rfl⟩

def cochainKernelCoconeSequence : ShortComplex (Complex R) :=
  ShortComplex.mk (cochainKernelToCocone d) (cochainCoconeToIdentity d)
    (cochainKernelToCocone_condition d)

lemma cochainKernelCoconeSequence_shortExact [Epi d] :
    (cochainKernelCoconeSequence d).ShortExact where
  exact := (cochainKernelCoconeSequence d).exact_of_f_is_kernel
    (cochainKernelToCocone_isKernel d)
  mono_f := mono_of_isLimit_fork (cochainKernelToCocone_isKernel d)
  epi_g := cochainCoconeToIdentity_epi d

lemma cochainShortExact_quasiIso_inclusion (S : ShortComplex (Complex R))
    (hS : S.ShortExact) (h₃ : S.X₃.Acyclic) : QuasiIso S.f := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : Mono (homologyMap S.f i) :=
    (hS.homology_exact₁ (i - 1) i (by change i - 1 + 1 = i; omega)).mono_g
      ((h₃ (i - 1)).isZero_homology.eq_of_src _ _)
  have : Epi (homologyMap S.f i) :=
    (hS.homology_exact₂ i).epi_f ((h₃ i).isZero_homology.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

lemma cochainKernelToCocone_quasiIso [Epi d] : QuasiIso (cochainKernelToCocone d) := by
  have hc : (mappingCocone (𝟙 L)).Acyclic := SerrePositivity.cochainAcyclic_shift
    ((complex_quasiIso_iff_acyclic_cone R (𝟙 L)).mp (quasiIso_of_isIso _)) (-1)
  exact cochainShortExact_quasiIso_inclusion (cochainKernelCoconeSequence d)
    (cochainKernelCoconeSequence_shortExact d) hc

lemma cochainKernelCoconeLift_quasiIso [Epi d] {W : Complex R}
    (a : W ⟶ K) (ha : a ≫ d = 0) (hlim : IsLimit (KernelFork.ofι a ha)) :
    QuasiIso (mappingCocone.lift d a 0 (by simp [ha])) := by
  let e := hlim.conePointUniqueUpToIso (kernelIsKernel d)
  have he : e.hom ≫ kernel.ι d = a :=
    hlim.conePointUniqueUpToIso_hom_comp (kernelIsKernel d) WalkingParallelPair.zero
  have h : e.hom ≫ cochainKernelToCocone d =
      mappingCocone.lift d a 0 (by simp [ha]) := by
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgMappingCocone_hom_ext d
    · rw [Category.assoc, cochainKernelToCocone_fst, mappingCocone.lift_fst, he]
    · rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
        cochainKernelToCocone_snd, Cochain.comp_zero]
      apply Cochain.ext
      intro p q hpq
      simp only [Cochain.zero_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
        mappingCocone.lift_f_snd_v]
  rw [← h]
  exact quasiIso_comp e.hom (cochainKernelToCocone d)
    (hφ := quasiIso_of_isIso _) (hφ' := cochainKernelToCocone_quasiIso d)

end SerrePositivity.KST.LocalizingInvariants
