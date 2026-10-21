module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTransitionHomology
public import SerrePositivity.KST.LocalizingInvariants.CochainKernelHomology

/-!
概要：隣接 Postnikov 遷移の実 kernel と、標準 cycles 層からの比較射を構成する。
方針：実 kernel 短完全列と次数別の準同型性から、kernel の唯一のホモロジー層を得る。
規約：複体としての kernel を使う。使われ方：導来平方零拡大の層の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra

variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0] (n : ℤ)

def postnikovKernel : Complex R := kernel (postnikovTransition R B (n + 1) n (by omega)).hom

def postnikovKernelInclusion : postnikovKernel R B n ⟶ (postnikov R B (n + 1)).X :=
  kernel.ι _

instance postnikovKernelInclusion_mono : Mono (postnikovKernelInclusion R B n) := by
  change Mono (kernel.ι _)
  infer_instance

def postnikovLayerToKernel : postnikovLayer R B n ⟶ postnikovKernel R B n :=
  kernel.lift _ (postnikovLayerInclusion R B n) (postnikovLayerInclusion_transition_zero R B n)

lemma postnikovLayerToKernel_inclusion :
    postnikovLayerToKernel R B n ≫ postnikovKernelInclusion R B n =
      postnikovLayerInclusion R B n := kernel.lift_ι _ _ _

instance postnikovKernel_lowerBound : (postnikovKernel R B n).IsStrictlyGE (-(n + 1)) :=
  cochainKernel_lowerBound _ _

lemma postnikovKernelInclusion_quasiIsoAt :
    QuasiIsoAt (postnikovKernelInclusion R B n) (-(n + 1)) :=
  cochainKernelInclusion_quasiIsoAt _ _
    (((postnikov R B n).X).isZero_of_isGE (-n) _ (by omega))
    (((postnikov R B n).X).isZero_of_isGE (-n) _ (by omega))

lemma postnikovKernel_exactAt_above (i : ℤ) (hi : -(n + 1) < i) :
    (postnikovKernel R B n).ExactAt i := by
  let t := (postnikovTransition R B (n + 1) n (by omega)).hom
  let hS := cochainKernelSequence_shortExact t
  have : QuasiIsoAt t i := postnikovTransition_quasiIsoAt R B (n + 1) n (by omega) i
    (by omega)
  have hm : Mono (homologyMap t i) := by infer_instance
  refine hS.exactAt_X₁ i hm ?_
  intro j hj
  change j + 1 = i at hj
  change Epi (homologyMap t j)
  by_cases h : -n ≤ j
  · have : QuasiIsoAt t j := postnikovTransition_quasiIsoAt R B (n + 1) n (by omega) j h
    infer_instance
  · have hz := (postnikov R B n).X.isZero_of_isGE (-n) j (by omega)
    exact hz.epi _

lemma postnikovLayerToKernel_quasiIso : QuasiIso (postnikovLayerToKernel R B n) := by
  rw [quasiIso_iff]
  intro i
  by_cases hi : i = -(n + 1)
  · subst i
    have := postnikovKernelInclusion_quasiIsoAt R B n
    have : QuasiIsoAt (postnikovLayerToKernel R B n ≫ postnikovKernelInclusion R B n)
        (-(n + 1)) := by
      rw [postnikovLayerToKernel_inclusion]
      exact postnikovLayerInclusion_quasiIsoAt R B n
    exact quasiIsoAt_of_comp_right (postnikovLayerToKernel R B n)
      (postnikovKernelInclusion R B n) _
  · have hL : (postnikovLayer R B n).ExactAt i := by
      by_cases h : i < -(n + 1)
      · exact CochainComplex.exactAt_of_isGE _ (-(n + 1)) i h
      · exact CochainComplex.exactAt_of_isLE _ (-(n + 1)) i (by omega)
    apply (quasiIsoAt_iff_exactAt _ i hL).2
    by_cases h : i < -(n + 1)
    · exact CochainComplex.exactAt_of_isGE _ (-(n + 1)) i h
    · exact postnikovKernel_exactAt_above R B n i (by omega)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
