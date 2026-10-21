module

public import SerrePositivity.KST.LocalizingInvariants.CochainSeparatedBounds
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
概要：全射な複体射の実 kernel と、終域の零ホモロジー下での包含の準同型性。
方針：kernel 短完全列の長完全列で、包含のホモロジー射の単射・全射を得る。
規約：kernel は複体圏の実極限。使われ方：Postnikov 層と実 kernel の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants

variable {R : Type u} [CommRing R] {P T : Complex R} (f : P ⟶ T)

def cochainKernelSequence : ShortComplex (Complex R) :=
  ShortComplex.mk (kernel.ι f) f (kernel.condition f)

lemma cochainKernelSequence_shortExact [Epi f] : (cochainKernelSequence f).ShortExact :=
  { exact := (cochainKernelSequence f).exact_of_f_is_kernel (kernelIsKernel f)
    mono_f := by change Mono (kernel.ι f); infer_instance
    epi_g := by change Epi f; infer_instance }

lemma cochainKernel_lowerBound (k : ℤ) [P.IsStrictlyGE k] :
    (kernel f).IsStrictlyGE k := by
  apply (CochainComplex.isStrictlyGE_iff _ _).2
  intro i hi
  exact IsZero.of_mono ((kernel.ι f).f i) (P.isZero_of_isStrictlyGE k i hi)

lemma cochainKernelInclusion_quasiIsoAt [Epi f] (i : ℤ)
    (hi : IsZero (T.homology i)) (hp : IsZero (T.homology (i - 1))) :
    QuasiIsoAt (kernel.ι f) i := by
  let hS := cochainKernelSequence_shortExact f
  have : Mono (homologyMap (kernel.ι f) i) :=
    (hS.homology_exact₁ (i - 1) i (by change i - 1 + 1 = i; omega)).mono_g (hp.eq_of_src _ _)
  have : Epi (homologyMap (kernel.ι f) i) :=
    (hS.homology_exact₂ i).epi_f (hi.eq_of_tgt _ _)
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact isIso_of_mono_of_epi _

end SerrePositivity.KST.LocalizingInvariants
