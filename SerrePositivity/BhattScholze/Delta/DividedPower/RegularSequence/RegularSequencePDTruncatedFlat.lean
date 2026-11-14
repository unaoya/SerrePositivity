module

public import SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequence.RegularSequencePDTor
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import all Mathlib.Algebra.MonoidAlgebra.Defs
import all Mathlib.RingTheory.TensorProduct.Maps
import all Mathlib.RingTheory.TensorProduct.Quotient

/-!
# 標数 p の分冪表示への係数射の忠実平坦性

## 概要
分冪表示は、元の族の p 乗で割った係数環の上で忠実平坦。

## 方針
切断多項式環上の自由分冪代数の基底を、評価射に沿って底変換する。

## 規約
BS 著者版 Lemma 2.38、Construction 6.1 の式 (6)。

## 使われ方
結晶被覆の剰余による消滅の検出と Tor 振幅。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
namespace SerrePositivity.BhattScholze
open scoped TensorProduct

variable {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] {r : ℕ} (f : Fin r → R)

/-- 元の族の p 乗を課す係数商。評価射の像イデアルで表示する。 -/
abbrev DPTruncatedCoefficientQuotient := R ⧸
  (truncatedPolynomialIdeal R (Fin r) p).map (MvPolynomial.aeval f).toRingHom

/-- 概要：分冪表示を切断多項式上の通常の押し出しとして計算する。
方針：係数商とテンソルの比較を、分冪包と δ 除算包の比較 の多項式評価の表示へ合成する。
規約：BS 著者版 Lemma 2.38、Construction 6.1 の環模型。
使われ方：係数射の平坦性と標準脚の計算。 -/
def dpTruncatedModelEquiv (hp : (p : R) = 0) :
    let P := MvPolynomial (Fin r) R
    let T := P ⧸ truncatedPolynomialIdeal R (Fin r) p
    let G := DividedPowerAlgebra R (Fin r →₀ R)
    letI : Algebra P R := (MvPolynomial.aeval f).toRingHom.toAlgebra
    letI : Algebra T (DPTruncatedCoefficientQuotient (p := p) f) := adicQuotientAlgebra _ R
    letI : Algebra T G := freeDPTruncatedAlgebra hp
    DPTruncatedCoefficientQuotient (p := p) f ⊗[T] G ≃+* DPFamilyPresentation f := by
  let P := MvPolynomial (Fin r) R
  let I := truncatedPolynomialIdeal R (Fin r) p
  let T := P ⧸ I
  let G := DividedPowerAlgebra R (Fin r →₀ R)
  let Q := DPTruncatedCoefficientQuotient (p := p) f
  letI : Algebra P R := (MvPolynomial.aeval f).toRingHom.toAlgebra
  letI : Algebra P G := (MvPolynomial.aeval (fun i : Fin r =>
    DividedPowerAlgebra.dp R 1 (Finsupp.single i 1 : Fin r →₀ R))).toRingHom.toAlgebra
  letI : Algebra T G := freeDPTruncatedAlgebra hp
  letI : Module P T := (inferInstance : Algebra P T).toModule
  letI : Module P G := (inferInstance : Algebra P G).toModule
  letI : SMul P T := (inferInstance : Algebra P T).toSMul
  letI : SMul P G := (inferInstance : Algebra P G).toSMul
  letI : IsScalarTower P T G := IsScalarTower.of_algebraMap_eq (R := P) (S := T) (A := G) (fun _ => rfl)
  letI : Algebra T Q := adicQuotientAlgebra I R
  let eQ := Algebra.TensorProduct.quotIdealMapEquivQuotTensor R I
  let e₁ := Algebra.TensorProduct.congr (AlgEquiv.refl : G ≃ₐ[G] G) eQ
  let e₂ := Algebra.TensorProduct.cancelBaseChange P T G G R
  exact (Algebra.TensorProduct.comm T Q G).toRingEquiv.trans
    (e₁.toRingEquiv.trans (e₂.toRingEquiv.trans
      (dpFamilyPresentation_polynomialTensorEquiv f).toRingEquiv))

/-- 概要：p 乗係数商から分冪表示への標準射。
方針：切断多項式上の模型の係数脚を標準同型で送る。
規約：BS 著者版 Construction 6.1 の最後の射。
使われ方：標準脚を保持した忠実平坦性。 -/
def dpTruncatedCoefficientMap (hp : (p : R) = 0) :
    DPTruncatedCoefficientQuotient (p := p) f →+* DPFamilyPresentation f := by
  let P := MvPolynomial (Fin r) R
  let T := P ⧸ truncatedPolynomialIdeal R (Fin r) p
  let G := DividedPowerAlgebra R (Fin r →₀ R)
  letI : Algebra P R := (MvPolynomial.aeval f).toRingHom.toAlgebra
  letI : Algebra T (DPTruncatedCoefficientQuotient (p := p) f) := adicQuotientAlgebra _ R
  letI : Algebra T G := freeDPTruncatedAlgebra hp
  exact (dpTruncatedModelEquiv f hp).toRingHom.comp
    (algebraMap (DPTruncatedCoefficientQuotient (p := p) f)
      (DPTruncatedCoefficientQuotient (p := p) f ⊗[T] G))

/-- 概要：切断係数射は元の係数を保つ。
方針：模型のテンソルの係数脚を、評価射の係数の釣り合いで移す。
規約：BS 著者版 Construction 6.1 の式 (6) の標準脚。
使われ方：剰余 Frobenius との合成の同定。 -/
theorem dpTruncatedCoefficientMap_mk (hp : (p : R) = 0) (a : R) :
    dpTruncatedCoefficientMap f hp (Ideal.Quotient.mk _ a) =
      algebraMap R (DPFamilyPresentation f) a := by
  let P := MvPolynomial (Fin r) R
  let G := DividedPowerAlgebra R (Fin r →₀ R)
  letI : Algebra P R := (MvPolynomial.aeval f).toRingHom.toAlgebra
  letI : Algebra P G := (MvPolynomial.aeval (fun i : Fin r =>
    DividedPowerAlgebra.dp R 1 (Finsupp.single i 1 : Fin r →₀ R))).toRingHom.toAlgebra
  let I := truncatedPolynomialIdeal R (Fin r) p
  let T := P ⧸ I
  let Q := DPTruncatedCoefficientQuotient (p := p) f
  letI : Algebra T G := freeDPTruncatedAlgebra hp
  letI : Module P T := (inferInstance : Algebra P T).toModule
  letI : Module P G := (inferInstance : Algebra P G).toModule
  letI : SMul P T := (inferInstance : Algebra P T).toSMul
  letI : SMul P G := (inferInstance : Algebra P G).toSMul
  letI : IsScalarTower P T G :=
    IsScalarTower.of_algebraMap_eq (R := P) (S := T) (A := G) (fun _ => rfl)
  letI : Algebra T Q := adicQuotientAlgebra I R
  have hc : (1 : G) ⊗ₜ[P] a = algebraMap R G a ⊗ₜ[P] (1 : R) := by
    have he := (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := P) (A := G) (B := R)
      (MvPolynomial.C a)).symm
    change (1 : G) ⊗ₜ[P] (MvPolynomial.aeval f) (MvPolynomial.C a) =
      (MvPolynomial.aeval (fun i : Fin r => DividedPowerAlgebra.dp R 1
        (Finsupp.single i 1 : Fin r →₀ R))) (MvPolynomial.C a) ⊗ₜ[P] (1 : R) at he
    rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C] at he
    exact he
  dsimp only [dpTruncatedCoefficientMap, dpTruncatedModelEquiv]
  simp only [RingHom.comp_apply, RingEquiv.trans_apply, AlgEquiv.toRingEquiv_eq_coe,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv,
    RingHom.id_apply, map_one, AlgEquiv.coe_refl, id_eq,
    Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
    Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk,
    Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
  change dpFamilyPresentation_polynomialTensorEquiv f
    ((Algebra.TensorProduct.cancelBaseChange P T G G R)
      ((1 : G) ⊗ₜ[T] ((1 : T) ⊗ₜ[P] a))) = _
  rw [Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
  rw [hc]
  exact (dpFamilyPresentation_polynomialTensorEquiv f).commutes (algebraMap R G a)

/-- 概要：切断係数射は忠実平坦。
方針：分冪包と δ 除算包の比較 の切断多項式上の自由性と忠実性を底変換し、環同型で移す。
規約：BS 著者版 Lemma 2.38、Construction 6.1。
使われ方：結晶被覆の剰余の最後の平坦射。 -/
theorem dpTruncatedCoefficientMap_faithfullyFlat (hp : (p : R) = 0) :
    (dpTruncatedCoefficientMap f hp).FaithfullyFlat := by
  let P := MvPolynomial (Fin r) R
  let T := P ⧸ truncatedPolynomialIdeal R (Fin r) p
  let G := DividedPowerAlgebra R (Fin r →₀ R)
  let Q := DPTruncatedCoefficientQuotient (p := p) f
  letI : Algebra P R := (MvPolynomial.aeval f).toRingHom.toAlgebra
  letI : Algebra T Q := adicQuotientAlgebra _ R
  letI : Algebra T G := freeDPTruncatedAlgebra hp
  letI : Module.Free T G := freeDPTruncated_moduleFree hp
  letI : Module.FaithfullyFlat T G := by
    classical
    by_cases h : Nontrivial R
    · letI := h
      letI : Nontrivial G := (freeDPBasis (Fin r) R).repr.symm.injective.nontrivial
      infer_instance
    · letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp h
      exact { submodule_ne_top := fun _ hm => False.elim (hm.ne_top (Subsingleton.elim _ _)) }
  have hflat : (algebraMap Q (Q ⊗[T] G)).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  exact (RingHom.FaithfullyFlat.stableUnderComposition _ _ hflat
    (RingHom.FaithfullyFlat.of_bijective (dpTruncatedModelEquiv f hp).bijective))

end SerrePositivity.BhattScholze
