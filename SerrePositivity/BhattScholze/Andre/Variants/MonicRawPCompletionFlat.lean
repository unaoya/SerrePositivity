module

public import SerrePositivity.BhattScholze.Andre.Variants.MonicRawPerfectionFlat
public import SerrePositivity.BhattScholze.Prism.Perfection.PCompletedPerfection
public import SerrePositivity.CommutativeAlgebra.AdicCompletionOpenQuotient

/-!
# André E1・E2：補助 raw 包の p 進完備 δ 完全化の忠実平坦性

## 概要

完全 δ 係数環上の任意正次数モニック族について、補助 raw φ(f)/p 包の p 進完備 δ 完全化は
元の係数射に関して p 完全忠実平坦。BS Cor 2.39（著者版 p.25）、Rem 7.15（p.62）の準備。

## 方針

完備化の開イデアル商の比較で mod p の忠実平坦性を保ち、完全 δ 構造の p 正則性を使う。
原典の Prop 7.11 を用いる証明とは異なる経路の補助計算。

## 規約

対象は補助 φ(f)/p 包の完全化である。一般 f/d 包やその perfectoid 商との比較は含まない。

## 使われ方

最終 prismatic envelope の比較への補助的な p 完全忠実平坦性を供給する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open scoped TensorProduct
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (f : σ → Polynomial A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun s : σ => monicRelation (f s) s)
local notation "F" => deltaAdjoinDivisionStructure E (p : P)
  (fun s ↦ DeltaStructure.frobeniusLift E (r s))
local notation "C" => DeltaPerfection F
local notation "Z" => PCompletedDeltaPerfection F
local notation "I" => Ideal.span ({(p : A)} : Set A)
local notation "J" => Ideal.span ({(p : C)} : Set C)
local notation "Q" => A ⧸ I

/-- 概要：既存完備化の、完備化前の実δ完全化に関する標準代数構造。
方針：標準の古典的 p 進完備化の代数構造を使用する。
規約：局所導入し、元の係数作用を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の完備化前後の剰余比較。 -/
abbrev monicRawPCompletedPerfectionOverPerfection : Algebra C Z :=
  inferInstanceAs (Algebra C (AdicCompletion J C))

/-- 概要：元のraw係数射と既存のp進完備δ完全化標準射の合成。
方針：元の raw 係数射と既存の完備化射を合成する。
規約：実際の元の A 係数射を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の元の基底上の平坦性。 -/
def monicRawPCompletedPerfectionCoefficientMap : A →+* Z :=
  (pCompletedDeltaPerfectionMap F).comp (monicRawCoefficientMap D f)

/-- 概要：p進完備δ完全化の実A係数作用。
方針：明示した係数射から代数構造を定める。
規約：局所導入する。
使われ方：BS Rem 7.15（著者版 p.62）の剰余テンソルの元の係数作用。 -/
abbrev monicRawPCompletedPerfectionAlgebra : Algebra A Z :=
  (monicRawPCompletedPerfectionCoefficientMap D f).toAlgebra

attribute [local instance] monicRawPerfectionAlgebra monicRawPCompletedPerfectionAlgebra
  adicQuotientAlgebra monicRawPCompletedPerfectionOverPerfection
local notation "Kc" => Ideal.map (algebraMap A C) I
local notation "Kz" => Ideal.map (algebraMap A Z) I

/-- 概要：実係数作用は、完備化前の係数射と標準完備化射の合成。
方針：定義の一致による。
規約：第零段射の係数作用を使う。
使われ方：BS Rem 7.15（著者版 p.62）の完備化前後の係数比較。 -/
theorem monicRawPCompletedPerfectionCoefficientMap_comp :
    monicRawPCompletedPerfectionCoefficientMap D f =
      (algebraMap C Z).comp (monicRawPerfectionCoefficientMap D f) := rfl

/-- 概要：正確なA係数のp商を、完備化前後で比較する実環同型。
方針：拡張イデアルを p 主イデアルと同定し、開商の比較を使う。
規約：商環だけでなく元の係数像も次の補題で保持する。
使われ方：BS Rem 7.15（著者版 p.62）のmod p 忠実平坦性の保存。 -/
def monicRawPCompletedPerfectionResidueEquiv : Z ⧸ Kz ≃+* C ⧸ Kc := by
  have hc : Kc = J := by rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hz : Kz = Ideal.map (algebraMap C Z) J := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast,
      Ideal.map_span, Set.image_singleton, map_natCast]
  exact (Ideal.quotEquivOfEq hz).trans
    ((adicCompletionOpenQuotientEquiv J J 1 (by simp)
      (Submodule.fg_span (Set.toFinite _))).toRingEquiv.trans (Ideal.quotEquivOfEq hc.symm))

/-- 概要：実剰余同型は、元の完備化前の標準係数像を保つ。
方針：開商比較の標準完備化射に関する公式を使う。
規約：任意の完備化前の元を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の元の A/p 作用の比較。 -/
theorem monicRawPCompletedPerfectionResidueEquiv_mk (c : C) :
    monicRawPCompletedPerfectionResidueEquiv D f
      (Ideal.Quotient.mk Kz (algebraMap C Z c)) = Ideal.Quotient.mk Kc c := by
  unfold monicRawPCompletedPerfectionResidueEquiv
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, RingEquiv.trans_apply]
  change Ideal.quotEquivOfEq _
    (adicCompletionOpenQuotientMap J J 1 (by simp) (algebraMap C Z c)) = _
  rw [adicCompletionOpenQuotientMap_algebraMap, Ideal.quotEquivOfEq_mk]

local instance monicRawPCompletedPerfectionResidueAlgebra : Algebra Q (Z ⧸ Kz) :=
  adicQuotientAlgebra I Z
local instance monicRawPerfectionActualResidueAlgebra : Algebra Q (C ⧸ Kc) :=
  adicQuotientAlgebra I C

local instance monicRawPCompletedPerfectionResidueModule : Module Q (Z ⧸ Kz) := Algebra.toModule
local instance monicRawPerfectionActualResidueModule : Module Q (C ⧸ Kc) := Algebra.toModule

set_option maxHeartbeats 800000 in
-- 完備化前後の具体的商作用と係数射の照合に、既定値を超える簡約を要する。
/-- 概要：剰余比較は、元のA/pの標準作用について線形。
方針：剰余係数を代表元へ戻し、係数像の公式を使う。
規約：元の係数作用を別の作用に取り替えない。
使われ方：BS Rem 7.15（著者版 p.62）の忠実平坦性の移送。 -/
def monicRawPCompletedPerfectionResidueLinearEquiv : (Z ⧸ Kz) ≃ₗ[Q] C ⧸ Kc := by
  let : IsScalarTower A C Z := IsScalarTower.of_algebraMap_eq' rfl
  refine { (monicRawPCompletedPerfectionResidueEquiv D f).toAddEquiv with map_smul' := ?_ }
  intro c x
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  change monicRawPCompletedPerfectionResidueEquiv D f
    ((Ideal.Quotient.mk Kz (algebraMap A Z c)) * x) =
      (Ideal.Quotient.mk Kc (algebraMap A C c)) *
        monicRawPCompletedPerfectionResidueEquiv D f x
  rw [map_mul, IsScalarTower.algebraMap_apply A C Z,
    monicRawPCompletedPerfectionResidueEquiv_mk]

/-- 概要：通常の正確な標準剰余テンソルも、完備化前後でA/p線形に同型。
方針：商テンソル比較と剰余の線形比較を合成する。
規約：元の標準係数射に沿う通常テンソルを使う。
使われ方：BS Rem 7.15（著者版 p.62）の主元判定の剰余入力。 -/
def monicRawPCompletedPerfectionResidueTensorEquiv :
    (Q ⊗[A] Z) ≃ₗ[Q] Q ⊗[A] C :=
  ((quotientTensorReductionEquiv I Z).trans (adicReductionEquivAlgebraQuotient I Z)).trans
    ((monicRawPCompletedPerfectionResidueLinearEquiv D f).trans
      ((quotientTensorReductionEquiv I C).trans (adicReductionEquivAlgebraQuotient I C)).symm)

/-- 概要：通常剰余テンソルの忠実平坦性は、既存p進完備δ完全化へ保存される。
方針：前工程の δ 完全化の忠実平坦性を標準剰余線形比較で移す。
規約：完全基底上の正次数モニック任意族を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の補助包の p 完全忠実平坦性。 -/
theorem monicRawPCompletedPerfection_residueTensor_faithfullyFlat
    (hD : D.IsPerfect) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) (hdp : D.IsDistinguished (p : A)) :
    Module.FaithfullyFlat Q (Q ⊗[A] Z) := by
  have := monicRawPerfection_residueTensor_faithfullyFlat D f hD hf hdeg hdp
  exact Module.FaithfullyFlat.of_linearEquiv Q (Q ⊗[A] C)
    (monicRawPCompletedPerfectionResidueTensorEquiv D f)

/-- 概要：p進完備δ完全化のp正則性は、元のAのpスカラーについても成り立つ。
方針：完全 δ 構造の p 正則性と係数射の自然数保存を使う。
規約：この正則性にはモニック性を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の主元判定の Tor 消滅入力。 -/
theorem monicRawPCompletedPerfection_p_smul_regular : IsSMulRegular Z (p : A) := by
  intro x y h
  apply (pCompletedDeltaPerfection_isPerfect F).p_mul_injective
  simp only [Algebra.smul_def, map_natCast] at h
  exact h

/-- 概要：完全係数環の任意正次数モニック族の補助 raw 包の p 進完備 δ 完全化は p 完全忠実平坦。
方針：p 正則性と通常剰余テンソルの忠実平坦性を主元判定に渡す。
規約：正次数モニック族の補助 φ(f)/p 包の結果である。
使われ方：BS Rem 7.15（著者版 p.62）の最終 f/d 包との比較への準備。 -/
theorem monicRawPCompletedPerfection_isCompletelyFaithfullyFlat
    (hD : D.IsPerfect) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) (hdp : D.IsDistinguished (p : A)) :
    IsCompletelyFaithfullyFlat I Z :=
  isCompletelyFaithfullyFlat_principal_of_regular (p : A) hD.p_mul_injective Z
    (monicRawPCompletedPerfection_p_smul_regular D f)
    (monicRawPCompletedPerfection_residueTensor_faithfullyFlat D f hD hf hdeg hdp)

end SerrePositivity.BhattScholze.Andre
