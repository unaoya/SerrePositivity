module
public import SerrePositivity.HomologicalAlgebra.BoundedTermKoszulAcyclic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Canonical Koszul comparison from a bounded augmented complex -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type u} [CommRing C]

/-- A kernel term is the original source term when the target term vanishes. -/
def kernelTermIsoOfTargetZero {K L : CochainComplex (ModuleCat.{u} C) ℤ}
    (f : K ⟶ L) (q : ℤ) (hL : IsZero (L.X q)) : (kernel f).X q ≅ K.X q := by
  have h : f.f q = 0 := hL.eq_zero_of_tgt _
  exact PreservesKernel.iso (eval (ModuleCat.{u} C) (.up ℤ) q) f ≪≫
    eqToIso (congrArg (fun g : K.X q ⟶ L.X q => kernel g) h) ≪≫ kernelZeroIsoSource

/-- A componentwise monomorphism has zero kernel term at that degree. -/
lemma kernelTerm_isZero_of_mono {K L : CochainComplex (ModuleCat.{u} C) ℤ}
    (f : K ⟶ L) (q : ℤ) [Mono (f.f q)] : IsZero ((kernel f).X q) :=
  (isZero_kernel_of_mono (f.f q)).of_iso
    (PreservesKernel.iso (eval (ModuleCat.{u} C) (.up ℤ) q) f)

/-- If a bounded nonnegative augmented complex identifies its zero term, and its positive
terms are Koszul-acyclic, applying the parameter Koszul functor to its actual augmentation
is a quasi-isomorphism. -/
lemma boundedKoszulAugmentation_quasiIso {r : ℕ} (y : Fin r → C)
    (K : CochainComplex (ModuleCat.{u} C) ℤ) (M : ModuleCat.{u} C)
    (f : K ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} C) 0).obj M)
    [IsIso (f.f 0)] (N : ℕ)
    (hlo : ∀ q : ℤ, q < 0 → IsZero (K.X q))
    (hhi : ∀ q : ℤ, (N : ℤ) < q → IsZero (K.X q))
    (hterms : ∀ q : ℤ, 0 < q → ∀ p : ℤ,
      IsZero (((koszulModuleFunctor y).obj (K.X q)).homology p)) :
    QuasiIso ((koszulFunctor y).map f) := by
  have hnonpos (q : ℤ) (hq : q ≤ 0) : IsZero ((kernel f).X q) := by
    by_cases hqzero : q = 0
    · subst q
      exact kernelTerm_isZero_of_mono f 0
    · exact IsZero.of_mono ((kernel.ι f).f q) (hlo q (by omega))
  have hker := boundedTermKoszul_homology_isZero y N (kernel f) 1
    (fun q hq => hnonpos q (by omega))
    (fun q hq => IsZero.of_mono ((kernel.ι f).f q) (hhi q (by omega))) (by
      intro q p
      by_cases hq : q ≤ 0
      · exact ((koszulModuleFunctor y) ⋙ homologyFunctor (ModuleCat.{u} C) (.up ℤ) p).map_isZero
          (hnonpos q hq)
      · exact (hterms q (by omega) p).of_iso
          (((koszulModuleFunctor y) ⋙ homologyFunctor (ModuleCat.{u} C) (.up ℤ) p).mapIso
            (kernelTermIsoOfTargetZero f q
              (isZero_single_obj_X (.up ℤ) 0 M q (by omega)))))
  have : Epi f := epi_of_epi_f f (by
    intro q
    by_cases hq : q = 0
    · subst q; infer_instance
    · exact (isZero_single_obj_X (.up ℤ) 0 M q hq).epi _)
  let S : ShortComplex (CochainComplex (ModuleCat.{u} C) ℤ) :=
    ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel f }
  have hSy := koszulFunctor_shortExact y S hS
  rw [quasiIso_iff]
  intro p
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : Mono (homologyMap ((koszulFunctor y).map f) p) :=
    (hSy.homology_exact₂ p).mono_g ((hker p).eq_zero_of_src _)
  have : Epi (homologyMap ((koszulFunctor y).map f) p) :=
    (hSy.homology_exact₃ p (p + 1) rfl).epi_f ((hker (p + 1)).eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

end SerrePositivity
