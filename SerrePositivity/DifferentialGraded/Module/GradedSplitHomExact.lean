module
public import SerrePositivity.DifferentialGraded.Module.GradedSplitElements
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # 次数付き分裂に対するHom endのkernelの同定 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
namespace ModuleGradedSplit
variable {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}

/-- 商のsectionへの前合成。Hom複体のchain mapとは要求しない。 -/
def homKernelRetraction (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D)
    (q : ℤ) (z : (moduleHom A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) T)).X q) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) P)
      (ForgetEnrichment.to (Complex A) T)).X q :=
  forward A (x := ForgetEnrichment.to (Complex A) P)
    (y := ForgetEnrichment.to (Complex A) N) (z := ForgetEnrichment.to (Complex A) T)
    s.sectionElement z (zero_add q)

lemma homKernelRetraction_π (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D)
    (q : ℤ) (z : (moduleHom A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) T)).X q) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) P)
      (ForgetEnrichment.to (Complex A) T) x).f q (s.homKernelRetraction T q z) =
      (Cochain.ofHoms (s.section_ x)).comp
        ((moduleHomπ A D (ForgetEnrichment.to (Complex A) N)
          (ForgetEnrichment.to (Complex A) T) x).f q z) (zero_add q) := by
  rw [homKernelRetraction, moduleHomForward_π, zero_mul, Int.negOnePow_zero,
    one_smul, s.sectionElement_π]

lemma homKernel_retraction (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D)
    (q : ℤ) (z : (moduleHom A D (ForgetEnrichment.to (Complex A) P)
      (ForgetEnrichment.to (Complex A) T)).X q) :
    s.homKernelRetraction T q ((eHomWhiskerRight (Complex A) g T).f q z) = z := by
  apply moduleHomElement_ext A D (M := ForgetEnrichment.to (Complex A) P)
    (N := ForgetEnrichment.to (Complex A) T)
  intro x
  rw [s.homKernelRetraction_π, moduleHomWhiskerRight_apply_π A D g q z x]
  apply Cochain.ext
  intro i j hij
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.ofHoms_v]
  rw [← Category.assoc, s.section_projection, Category.id_comp]

lemma homKernel_injective (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D)
    (q : ℤ) : Function.Injective ((eHomWhiskerRight (Complex A) g T).f q) := by
  intro z w h
  have he := congrArg (s.homKernelRetraction T q) h
  simpa only [s.homKernel_retraction] using he

lemma homKernel_of_restriction_zero (s : ModuleGradedSplit A D f g)
    (T : ModuleCategory A D) (q : ℤ)
    (z : (moduleHom A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) T)).X q)
    (hz : (eHomWhiskerRight (Complex A) f T).f q z = 0) :
    (eHomWhiskerRight (Complex A) g T).f q (s.homKernelRetraction T q z) = z := by
  apply moduleHomElement_ext A D (M := ForgetEnrichment.to (Complex A) N)
    (N := ForgetEnrichment.to (Complex A) T)
  intro x
  rw [moduleHomWhiskerRight_apply_π A D g q _ x, s.homKernelRetraction_π]
  apply Cochain.ext
  intro i j hij
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.ofHoms_v]
  have hx := congrArg (fun a => (moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) T) x).f q a) hz
  rw [moduleHomWhiskerRight_apply_π A D f q z x, map_zero] at hx
  have hxi := congrArg (fun a => a.v i j hij) hx
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.zero_v] at hxi
  have hd := congrArg (fun a => a ≫
    ((moduleHomπ A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) T) x).f q z).v i j hij) (s.decomposition x i)
  rw [Preadditive.add_comp, Category.id_comp, Category.assoc, hxi,
    comp_zero, zero_add] at hd
  exact (Category.assoc _ _ _).symm.trans hd

lemma homKernel_restriction_zero (s : ModuleGradedSplit A D f g)
    (T : ModuleCategory A D) (q : ℤ)
    (z : (moduleHom A D (ForgetEnrichment.to (Complex A) P)
      (ForgetEnrichment.to (Complex A) T)).X q) :
    (eHomWhiskerRight (Complex A) f T).f q
      ((eHomWhiskerRight (Complex A) g T).f q z) = 0 := by
  apply moduleHomElement_ext A D (M := ForgetEnrichment.to (Complex A) M)
    (N := ForgetEnrichment.to (Complex A) T)
  intro x
  rw [moduleHomWhiskerRight_apply_π A D f q _ x,
    moduleHomWhiskerRight_apply_π A D g q z x, map_zero]
  apply Cochain.ext
  intro i j hij
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.zero_v]
  have hfg := congrArg (fun a => ((moduleEvaluation A D x).map a).f i)
    s.inclusion_projection
  simp only [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f,
    CategoryTheory.Functor.map_zero, HomologicalComplex.zero_f] at hfg
  rw [← Category.assoc, hfg, zero_comp]

/-- Homは全次数分裂する拡大を複体の短複体へ送る。 -/
def homShortComplex (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D) :
    ShortComplex (Complex A) :=
  ShortComplex.mk (eHomWhiskerRight (Complex A) g T)
    (eHomWhiskerRight (Complex A) f T) (by
      apply HomologicalComplex.Hom.ext
      funext q
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact s.homKernel_restriction_zero T q z)

lemma homShortComplex_degreewise_shortExact (s : ModuleGradedSplit A D f g)
    (T : ModuleCategory A D) (q : ℤ) :
    ((s.homShortComplex T).map
      (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) q)).ShortExact where
  exact := by
    apply (ShortComplex.moduleCat_exact_iff _).2
    intro z hz
    exact ⟨s.homKernelRetraction T q z, s.homKernel_of_restriction_zero T q z hz⟩
  mono_f := (ModuleCat.mono_iff_injective _).2 (s.homKernel_injective T q)
  epi_g := (ModuleCat.epi_iff_surjective _).2 (s.homRestriction_surjective T q)

lemma homShortComplex_shortExact (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D) :
    (s.homShortComplex T).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (s.homShortComplex_degreewise_shortExact T)

end ModuleGradedSplit
end SerrePositivity.DifferentialGraded
