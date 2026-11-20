module

public import SerrePositivity.AlgebraicGeometry.ResidueTensorInjectivity
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Ring.NonZeroDivisors

/-!
概要：KST §5、Stacks 05DH・0810 の閉ファイバーによる分裂代数の正則元。
方針：閉ファイバーの非零元による乗法の単射性を分裂表示で持ち上げる。
規約：分裂表示と閉ファイバーの整域性を明示する。
使われ方：拡大極大イデアルでの特別な局所化への単射性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R B : Type*} [CommRing R] [IsLocalRing R] [CommRing B] [Algebra R B]
  {ι : Type*} (e : B →ₗ[R] (ι →₀ R)) (p : (ι →₀ R) →ₗ[R] B)
  (hpe : p.comp e = LinearMap.id)
  [IsDomain ((IsLocalRing.ResidueField R) ⊗[R] B)]

include e p hpe

/--
概要：閉ファイバーで非零となる分裂代数の元は正則。
方針：乗法写像の剰余体への基底変更を実際のファイバー環の乗法と同定する。
規約：KST §5、Stacks 05DH, Lemma 38.7.4・0810, Lemma 38.30.2 の特殊形。
使われ方：閉ファイバーの一般点での局所化の単射性。
-/
theorem splitAlgebra_isRegular_of_residue_tmul_ne_zero (s : B)
    (hs : (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] s ≠ 0) : IsRegular s := by
  let k := IsLocalRing.ResidueField R
  let D := k ⊗[R] B
  let f : B →ₗ[R] B := Algebra.lsmul R R B s
  let : Module.Flat R B := Module.Flat.of_retract e p hpe
  have hmap : f.baseChange k = Algebra.lsmul k k D ((1 : k) ⊗ₜ[R] s) := by
    ext b
    change (1 : k) ⊗ₜ[R] (s * b) = ((1 : k) ⊗ₜ[R] s) * ((1 : k) ⊗ₜ[R] b)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hf : Function.Injective (f.baseChange k) := by
    rw [hmap]
    intro x y hxy
    change ((1 : k) ⊗ₜ[R] s) * x = ((1 : k) ⊗ₜ[R] s) * y at hxy
    exact mul_left_cancel₀ hs hxy
  have hinj : IsLeftRegular s :=
    injective_of_residueTensor_injective_of_retract e p hpe f hf
  exact ⟨hinj, hinj.right_of_commute (fun _ => mul_comm _ _)⟩

/--
概要：極大イデアルの拡大の外の元は分裂代数上の非零因子。
方針：剰余体テンソル写像の核を拡大極大イデアルと同定して正則性を適用する。
規約：KST §5、Stacks 05DH・0810、閉ファイバーは整域とする。
使われ方：特別な局所化の分母の正則性。
-/
theorem splitAlgebra_isRegular_of_not_mem_extended_maximalIdeal (s : B)
    (hs : s ∉ (IsLocalRing.maximalIdeal R).map (algebraMap R B)) : IsRegular s := by
  apply splitAlgebra_isRegular_of_residue_tmul_ne_zero e p hpe s
  intro hz
  have hmem : s ∈ LinearMap.ker
      (TensorProduct.mk R (IsLocalRing.ResidueField R) B 1) := hz
  change s ∈ LinearMap.ker (TensorProduct.mk R
    (R ⧸ IsLocalRing.maximalIdeal R) B 1) at hmem
  rw [LinearMap.ker_tensorProductMk, Ideal.smul_top_eq_map] at hmem
  exact hs hmem

/--
概要：拡大極大イデアルによる特別な局所化への実際の写像は単射。
方針：全ての分母が正則であることを局所化の単射性判定へ渡す。
規約：KST §5、Stacks 05DH・0810、分裂表示と閉ファイバーの整域性を使う。
使われ方：高次小行列式の消滅を特別な局所環で検出する。
-/
theorem splitAlgebra_extendedMaximalLocalization_injective
    [((IsLocalRing.maximalIdeal R).map (algebraMap R B)).IsPrime] :
    Function.Injective (algebraMap B
      (Localization.AtPrime ((IsLocalRing.maximalIdeal R).map (algebraMap R B)))) := by
  apply IsLocalization.injective
    (M := ((IsLocalRing.maximalIdeal R).map (algebraMap R B)).primeCompl)
    (Localization.AtPrime ((IsLocalRing.maximalIdeal R).map (algebraMap R B)))
  intro s hs
  exact isRegular_iff_mem_nonZeroDivisors.mp
    (splitAlgebra_isRegular_of_not_mem_extended_maximalIdeal e p hpe s hs)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
