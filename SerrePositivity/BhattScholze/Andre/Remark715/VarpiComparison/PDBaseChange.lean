module

public import SerrePositivity.BhattScholze.Andre.Remark715.PerfectPrismVarpiNativePDFlat
public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.MonicPDEnvelope
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# BS Rem 7.15（著者版 p.62）：pd 表示環の係数テンソル底変換

## 概要
無限根環上の主 pd 表示は係数の主イデアル商による底変換と可換である。
完全 prism の既存の A/p 係数表示を、実際の R/ϖ テンソル積として比較する。

## 方針
通常商とテンソル積の同型を、検証済みの pd 表示の係数商同型へ合成する。
全分冪生成元の値と原典側の実分冪構造を同じ台環で保持する。

## 規約
R=A/(d) と A/p を区別する。一般の表示環同型に正則性は不要だが、
原典側の実分冪構造には射影的係数商による無条件版を用いる。
原典の p ねじれなしへの帰着とは異なる証明経路。

## 使われ方
R/p から R/ϖ への係数商、および実装の A/p 表示と原典の R/ϖ 表示の照合。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre.VarpiComparison
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2048

section General
variable (S : Type u) [CommRing S] (p : ℕ) (hp : 0 < p) (c : S) (f : Polynomial S)
local notation "N" => PowerRootPolynomial S p hp
local notation "z" => powerRootPolynomialBaseMap S p hp f
local notation "D" => PrincipalDPPresentation N z
local notation "Q" => S ⧸ Ideal.span {(c : S)}
local notation "NQ" => PowerRootPolynomial Q p hp
local notation "zQ" => powerRootPolynomialBaseMap Q p hp (f.map (Ideal.Quotient.mk _))

/-- 概要：無限根環の pd 表示を係数商へテンソルすると、同じ入力の pd 表示となる。
方針：通常テンソル商の同型と既存の二重商交換を合成する。
規約：任意の係数環・入力で成立する台環同型である。
使われ方：BS Rem 7.15（著者版 p.62）の R/p から R/ϖ への底変換。 -/
def powerRootPDTensorQuotientEquiv : Q ⊗[S] D ≃+* PrincipalDPPresentation NQ zQ :=
  ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor D (Ideal.span {c})).symm.toRingEquiv.trans
    (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton]))).trans
      (principalDPReducedCoefficientEquiv (algebraMap S N c) z (algebraMap S D c)
        (IsScalarTower.algebraMap_apply S N D c)
        (powerRootCoefficientQuotientEquiv S p hp c) zQ (by
          rw [powerRootCoefficientQuotientEquiv_mk, powerRootCoefficientQuotientMap_baseMap]))

/-- 概要：係数テンソル比較はすべての標準分冪生成元を保つ。
方針：商テンソルの代表元公式と既存の生成元公式を使う。
規約：次数零も含む。
使われ方：BS Rem 7.15（著者版 p.62）の pd 構造の係数変更。 -/
theorem powerRootPDTensorQuotientEquiv_generator (i : ℕ) :
    powerRootPDTensorQuotientEquiv S p hp c f (1 ⊗ₜ[S] principalDPGenerator z i) =
      principalDPGenerator zQ i := by
  rw [← Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk D (Ideal.span {c})]
  simp only [powerRootPDTensorQuotientEquiv, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv,
    AlgEquiv.symm_apply_apply, Ideal.quotEquivOfEq_mk,
    principalDPReducedCoefficientEquiv_generator]
end General

/-- 概要：R/p の ϖ 還元は R/ϖ と標準的に同型。
方針：(ϖ^n)=(c) から (c)⊆(ϖ) を得て第三同型定理を使う。
規約：c=p とすると R/p から原典係数への商が得られる。
使われ方：BS Rem 7.15（著者版 p.62）の一般テンソル比較を R/p へ適用する係数同定。 -/
def primeVarpiDoubleQuotientEquiv {R : Type u} [CommRing R]
    (v c : R) (n : ℕ) (hn : 0 < n) (hspan : Ideal.span {v ^ n} = Ideal.span {c}) :
    ((R ⧸ Ideal.span {c}) ⧸ Ideal.span {Ideal.Quotient.mk (Ideal.span {c}) v}) ≃+*
      R ⧸ Ideal.span {v} :=
  (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans
    (DoubleQuot.quotQuotEquivQuotOfLE (show Ideal.span {c} ≤ Ideal.span {v} by
      rw [← hspan]
      exact Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self v (Nat.ne_of_gt hn))))

section Prism
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "R₀" => A ⧸ Ideal.span {(p : A)}
local notation "x" => Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW)
local notation "Q" => R₀ ⧸ Ideal.span {x}
local notation "D" => PowerRootCoefficientPDEnvelope p f
local notation "Rv" => (A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}
local notation "Nv" => PowerRootPolynomial Rv p hp
local notation "barr" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW})) (Ideal.Quotient.mk W.ideal)
local notation "zv" => powerRootPolynomialBaseMap Rv p hp (f.map barr)
local notation "Dv" => PrincipalDPPresentation Nv zv

/-- 概要：原典の R/ϖ に A/p の自然な係数作用を入れる。
方針：(A/p)/(x)≃R/ϖ と標準商射を合成する。
規約：x=φ⁻¹(d) mod p であり、R/p と A/p を混同しない。
使われ方：BS Rem 7.15（著者版 p.62）の実係数テンソル。 -/
@[instance_reducible] def varpiCoefficientAlgebra : Algebra R₀ Rv :=
  (((perfectPrismVarpiQuotientEquiv W hW).symm.toRingHom).comp
    (Ideal.Quotient.mk (Ideal.span {x}))).toAlgebra

/-- 概要：既存の係数商同型は A/p 代数同型である。
方針：自然な係数作用の定義を使う。
規約：順方向は (A/p)/(x) から R/ϖ。
使われ方：BS Rem 7.15（著者版 p.62）のテンソル因子の比較。 -/
def varpiCoefficientAlgEquiv :
    let := varpiCoefficientAlgebra W hW
    Q ≃ₐ[R₀] Rv := by
  let := varpiCoefficientAlgebra W hW
  exact { (perfectPrismVarpiQuotientEquiv W hW).symm with commutes' := fun _ => rfl }

/-- 概要：実装の A/p 係数 pd 包を R/ϖ へ底変換すると原典の同じ pd 表示環となる。
方針：係数商代数同型でテンソル因子を移し、既存の pd 係数商比較へ合成する。
規約：ϖ^p=p·単元による R/ϖ の係数作用を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の二つの係数表記の実同型。 -/
def perfectPrismPDTensorVarpiEquiv :
    let := varpiCoefficientAlgebra W hW
    Rv ⊗[R₀] D ≃+* Dv := by
  let := varpiCoefficientAlgebra W hW
  exact ((Algebra.TensorProduct.congr (varpiCoefficientAlgEquiv W hW).symm
    (AlgEquiv.refl : D ≃ₐ[R₀] D)).toRingEquiv.trans
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor D (Ideal.span {x})).symm.toRingEquiv).trans
        ((Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans
          (perfectPrismVarpiPDEnvelopeEquiv W hW f))

/-- 概要：原典係数へのテンソル比較は元の pd 包の全ての元で既存の係数商比較に一致する。
方針：テンソル因子変更と商テンソル同型の代表元公式を使う。
規約：生成元だけでなく環の全ての元を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の自然な pd 底変換射の照合。 -/
theorem perfectPrismPDTensorVarpiEquiv_one_tmul (t : D) :
    let := varpiCoefficientAlgebra W hW
    perfectPrismPDTensorVarpiEquiv W hW f (1 ⊗ₜ[R₀] t) =
      perfectPrismVarpiPDEnvelopeEquiv W hW f
        (Ideal.Quotient.mk (Ideal.span {algebraMap R₀ D x}) t) := by
  let := varpiCoefficientAlgebra W hW
  simp only [perfectPrismPDTensorVarpiEquiv, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one]
  rw [← Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk D (Ideal.span {x}),
    AlgEquiv.symm_apply_apply, Ideal.quotEquivOfEq_mk]
  rfl

/-- 概要：原典係数へのテンソル底変換は全標準分冪生成元を保つ。
方針：テンソル写像と商代表元の公式を順に用いる。
規約：モニック性も正則性も必要としない。
使われ方：BS Rem 7.15（著者版 p.62）の pd 包としての構造照合。 -/
theorem perfectPrismPDTensorVarpiEquiv_generator (i : ℕ) :
    let := varpiCoefficientAlgebra W hW
    perfectPrismPDTensorVarpiEquiv W hW f
      (1 ⊗ₜ[R₀] principalDPGenerator (powerRootCoefficientPDInput p f) i) =
        principalDPGenerator zv i := by
  let := varpiCoefficientAlgebra W hW
  rw [perfectPrismPDTensorVarpiEquiv_one_tmul]
  exact perfectPrismVarpiPDEnvelopeEquiv_generator W hW f i

/-- 概要：底変換した実テンソル環に原典側と同じ分冪構造を与える。
方針：全生成元を保つ同型で既存の実分冪構造を戻す。
規約：正次数イデアルは同型の逆像で固定し、モニック性のみを要求する。
使われ方：BS Rem 7.15（著者版 p.62）の pd 包の係数底変換。 -/
def perfectPrismPDTensorVarpiDividedPowers
    (hf : f.Monic) :
    let := varpiCoefficientAlgebra W hW
    DividedPowers ((principalDPPositiveIdeal zv).map
      (perfectPrismPDTensorVarpiEquiv W hW f).symm.toRingHom) := by
  let := varpiCoefficientAlgebra W hW
  exact DividedPowers.ofRingEquiv rfl
    (perfectPrismVarpiNativeDividedPowers_of_unconditional W hW f hf)

/-- 概要：底変換した実分冪構造で、入力の分冪は還元前の標準生成元の像になる。
方針：環同型の移送公式と全標準生成元の一致を使う。
規約：モニック性のみを要求し、元の入力と生成元を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の pd 包としての底変換の具体的計算。 -/
theorem perfectPrismPDTensorVarpiDividedPowers_generator
    (hf : f.Monic) (i : ℕ) :
    let := varpiCoefficientAlgebra W hW
    (perfectPrismPDTensorVarpiDividedPowers W hW f hf).dpow i
      (1 ⊗ₜ[R₀] algebraMap (PowerRootPolynomial R₀ p hp) D (powerRootCoefficientPDInput p f)) =
        1 ⊗ₜ[R₀] principalDPGenerator (powerRootCoefficientPDInput p f) i := by
  let := varpiCoefficientAlgebra W hW
  let e := perfectPrismPDTensorVarpiEquiv W hW f
  change e.symm ((perfectPrismVarpiNativeDividedPowers_of_unconditional W hW f hf).dpow i
    (e (1 ⊗ₜ[R₀] algebraMap (PowerRootPolynomial R₀ p hp) D
      (powerRootCoefficientPDInput p f)))) = _
  have hInput : e (1 ⊗ₜ[R₀] algebraMap (PowerRootPolynomial R₀ p hp) D
      (powerRootCoefficientPDInput p f)) = algebraMap Nv Dv zv := by
    simpa only [principalDPGenerator_one] using perfectPrismPDTensorVarpiEquiv_generator W hW f 1
  rw [hInput, perfectPrismVarpiNativeDividedPowers_base_apply_of_unconditional]
  apply e.injective
  rw [e.apply_symm_apply]
  exact (perfectPrismPDTensorVarpiEquiv_generator W hW f i).symm

end Prism
end SerrePositivity.BhattScholze.Andre.VarpiComparison
