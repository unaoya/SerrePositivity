module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.KProjectiveObstruction
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ProjectiveCokernelLifting
public import SerrePositivity.HomotopicalAlgebra.Complexes.ProjectiveModel
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# K-projective cokernel による射影 cofibration 判定

概要：各次数射影の K-projective cokernel を持つ単射は実射影 cofibration。
方針：次数ごとに持ち上げ、非輪状 kernel への全障害 cocycle を消す。
規約：非有界複体を扱い、モデル構造は仮定しない。
使われ方：正規化境界の実 cofibrancy の証明。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CochainComplex _root_.CochainComplex.HomComplex _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

lemma projectiveCofibration_of_projectiveCokernel {W Z : Complex A} (i : W ⟶ Z)
    [Mono i] [∀ n : ℤ, Projective ((cokernel i).X n)] [(cokernel i).IsKProjective] :
    (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp i := by
  intro X Y p hp
  rw [_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations_rlp] at hp
  have (n : ℤ) : Epi (p.f n) := (ModuleCat.epi_iff_surjective _).mpr (hp.1 n)
  have : Epi p := epi_of_epi_f p inferInstance
  have : QuasiIso p := hp.2
  constructor
  intro t b sq
  have hsq (n : ℤ) := sq.map (HomologicalComplex.eval _ _ n)
  have (n : ℤ) : Projective (cokernel (i.f n)) :=
    Projective.of_iso (asIso (cokernelComparison i (HomologicalComplex.eval _ _ n))).symm
      (inferInstanceAs (Projective ((cokernel i).X n)))
  have hL (n : ℤ) : HasLiftingProperty (i.f n) (p.f n) :=
    _root_.SerrePositivity.ComplexLimits.mono_projectiveCokernel_lifting _ _
  let lifts (n : ℤ) : (hsq n).LiftStruct := (hL n).sq_hasLift (hsq n) |>.exists_lift.some
  let β : Cocycle (cokernel i) (kernel p) 1 :=
    Lifting.cocycle₁ sq lifts (cokernelIsCokernel i) (kernelIsKernel p)
      (hπ := by simp) (hι := by simp)
  have hk : (kernel p).Acyclic := by
    have h : (ShortComplex.mk _ _ (kernel.condition p)).ShortExact :=
      { exact := ShortComplex.exact_kernel p }
    exact h.acyclic_X₁ (by dsimp; infer_instance)
  obtain ⟨α, hα⟩ := _root_.SerrePositivity.ComplexLimits.kProjective_eq_delta_of_cocycle β hk 0 (by simp)
  exact Lifting.hasLift sq lifts (cokernelIsCokernel i) (kernelIsKernel p) α hα

end SerrePositivity.ComplexLimits
