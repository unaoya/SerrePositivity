module

public import SerrePositivity.BhattScholze.Delta.Free.PolynomialExpandFree
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # B4-6：任意元族のモニック冪根添加環

expand作用の自由加群を係数評価で基底変更し、指定した元のn乗根を持つ通常の環を作る。
この環のperfectoid性や完備性は結論しない。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
attribute [local instance] polynomialExpandAlgebra
variable (n : ℕ) (σ : Type u) (R : Type v) [CommRing R]

/-- 根添加のテンソル積で用いるexpand作用の加群構造を明示する。 -/
abbrev monicPowerFamilyExpandModule :
    Module (MvPolynomial σ R) (PolynomialExpandTarget n σ R) :=
  @Algebra.toModule (MvPolynomial σ R) (PolynomialExpandTarget n σ R)
    inferInstance inferInstance (polynomialExpandAlgebra n σ R)

attribute [local instance] monicPowerFamilyExpandModule

/-- X_s^n=c_sを課した通常の根添加環を、既存テンソル積の基底変更で実現する。 -/
def MonicPowerFamilyCover (c : σ → R) :=
  let : Algebra (MvPolynomial σ R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  @TensorProduct (MvPolynomial σ R) inferInstance R (PolynomialExpandTarget n σ R)
    inferInstance inferInstance inferInstance (monicPowerFamilyExpandModule n σ R)

instance monicPowerFamilyCoverCommRing (c : σ → R) : CommRing (MonicPowerFamilyCover n σ R c) := by
  let : Algebra (MvPolynomial σ R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  change CommRing (R ⊗[MvPolynomial σ R] PolynomialExpandTarget n σ R)
  infer_instance

instance monicPowerFamilyCoverAlgebra (c : σ → R) : Algebra R (MonicPowerFamilyCover n σ R c) := by
  let : Algebra (MvPolynomial σ R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  change Algebra R (R ⊗[MvPolynomial σ R] PolynomialExpandTarget n σ R)
  infer_instance

/-- 元c_sの指定したn乗根。 -/
def monicPowerFamilyRoot (c : σ → R) (s : σ) : MonicPowerFamilyCover n σ R c := by
  let : Algebra (MvPolynomial σ R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  exact TensorProduct.tmul (R := MvPolynomial σ R) (M := R)
    (N := PolynomialExpandTarget n σ R) 1 (ULift.up (MvPolynomial.X s))

/-- 指定した根は実際にc_sの像をn乗根として持つ。 -/
theorem monicPowerFamilyRoot_pow (c : σ → R) (s : σ) :
    monicPowerFamilyRoot n σ R c s ^ n = algebraMap R (MonicPowerFamilyCover n σ R c) (c s) := by
  let : Algebra (MvPolynomial σ R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  change (TensorProduct.tmul (R := MvPolynomial σ R) (M := R)
      (N := PolynomialExpandTarget n σ R) 1 (ULift.up (MvPolynomial.X s))) ^ n =
    c s ⊗ₜ[MvPolynomial σ R] (1 : PolynomialExpandTarget n σ R)
  rw [Algebra.TensorProduct.tmul_pow, one_pow]
  have h := TensorProduct.smul_tmul (R := MvPolynomial σ R)
    (MvPolynomial.X s : MvPolynomial σ R) (1 : R) (1 : PolynomialExpandTarget n σ R)
  have hL : (MvPolynomial.X s : MvPolynomial σ R) • (1 : R) = c s := by
    change MvPolynomial.aeval c (MvPolynomial.X s) * 1 = c s
    rw [MvPolynomial.aeval_X, mul_one]
  have hR : (MvPolynomial.X s : MvPolynomial σ R) • (1 : PolynomialExpandTarget n σ R) =
      (ULift.up (MvPolynomial.X s) : PolynomialExpandTarget n σ R) ^ n := by
    change ULift.up (MvPolynomial.expand n (MvPolynomial.X s)) * 1 =
      (ULift.up (MvPolynomial.X s) : PolynomialExpandTarget n σ R) ^ n
    rw [mul_one, MvPolynomial.expand_X]
    rfl
  rw [hL, hR] at h
  exact h.symm

/-- n>0なら通常の根添加環は係数環上自由。任意個の元を同時に扱う。 -/
theorem monicPowerFamilyCover_moduleFree (c : σ → R) (hn : 0 < n) :
    Module.Free R (MonicPowerFamilyCover n σ R c) := by
  let : Algebra (MvPolynomial σ R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  let := polynomialExpand_moduleFree n σ R hn
  change Module.Free R (R ⊗[MvPolynomial σ R] PolynomialExpandTarget n σ R)
  infer_instance

/-- 通常の根添加環は平坦。有限性・Noether性は不要。 -/
theorem monicPowerFamilyCover_moduleFlat (c : σ → R) (hn : 0 < n) :
    Module.Flat R (MonicPowerFamilyCover n σ R c) := by
  let := monicPowerFamilyCover_moduleFree n σ R c hn
  infer_instance

/-- 非零係数環では通常の根添加環は忠実平坦。 -/
theorem monicPowerFamilyCover_moduleFaithfullyFlat [Nontrivial R] (c : σ → R) (hn : 0 < n) :
    Module.FaithfullyFlat R (MonicPowerFamilyCover n σ R c) := by
  let : Algebra (MvPolynomial σ R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  let := polynomialExpand_moduleFaithfullyFlat n σ R hn
  change Module.FaithfullyFlat R (R ⊗[MvPolynomial σ R] PolynomialExpandTarget n σ R)
  infer_instance

/-- 零係数環も含む、通常根添加環の忠実平坦性。 -/
theorem monicPowerFamilyCover_moduleFaithfullyFlat_all (c : σ → R) (hn : 0 < n) :
    Module.FaithfullyFlat R (MonicPowerFamilyCover n σ R c) := by
  rcases subsingleton_or_nontrivial R with hs | hnR
  · let := hs
    rw [Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality]
    refine ⟨monicPowerFamilyCover_moduleFlat n σ R c hn, ?_⟩
    intro N _ _ _
    exact Module.subsingleton R N
  · let := hnR
    exact monicPowerFamilyCover_moduleFaithfullyFlat n σ R c hn

end SerrePositivity.BhattScholze
