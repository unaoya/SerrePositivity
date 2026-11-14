module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Delta.Free.FreeDeltaRing
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import SerrePositivity.BhattScholze.Delta.Free.PolynomialExpand
public import Mathlib.FieldTheory.Finite.Basic
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Torsion
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Criterion
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import SerrePositivity.CommutativeAlgebra.Koszul.Resolution

/-!
# 自由 δ 環の Frobenius の平坦性（BS 著者版 Lemma 2.11 の後半の p 完全版）

## 概要
自由整数 δ 環の mod p の Frobenius は自由で忠実平坦、Frobenius は p 完全忠実平坦。座標ごとの版
（L/(p,z) → L/(p,φ(z)) の忠実平坦性、(p,φ(z)) の正則性）。BS 著者版 Lemma 2.11 の Frobenius の忠実平坦性。

## 方針
mod p では Frobenius が expand 写像 x ↦ x^p に一致し、各指数が p 未満の単項式を基底とする自由加群。
p 完全忠実平坦性は共通基盤の判定（源と終域が p 正則、mod p が忠実平坦）から。

## 規約
本当の忠実平坦性は述べない。

## 使われ方
自由 δ 環の Frobenius の比較と BS 著者版 Lemma 2.36・Corollary 2.44 に関わる分冪包の計算に用いる。
-/

@[expose] public noncomputable section
universe u

/-! ## 自由整数δ環のmod pの具体的表示

係数を素数体へ写す標準射の核を(p)と計算し、標準商同型を構成する。
Frobeniusの平坦性への接続に使う。
-/

section FreeDeltaModP

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (σ : Type u)

/-- 自由整数δ環の係数を素数体へ写す標準射。 -/
def freeDeltaModPMap : FreeDeltaRing σ →+* MvPolynomial (σ × ℕ) (ZMod p) :=
  MvPolynomial.map (Int.castRingHom (ZMod p))

/-- 標準係数射は全射。 -/
theorem freeDeltaModPMap_surjective : Function.Surjective (freeDeltaModPMap p σ) :=
  MvPolynomial.map_surjective _ (ZMod.intCast_surjective (n := p))

/-- 標準係数射の核はpの単項イデアル。 -/
theorem freeDeltaModPMap_ker : RingHom.ker (freeDeltaModPMap p σ) =
    Ideal.span {(p : FreeDeltaRing σ)} := by
  apply le_antisymm
  · intro x hx
    change freeDeltaModPMap p σ x = 0 at hx
    have hcoeff (d : (σ × ℕ) →₀ ℕ) : (p : ℤ) ∣ x.coeff d := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      have he := congrArg (fun y : MvPolynomial (σ × ℕ) (ZMod p) ↦ y.coeff d) hx
      simpa only [freeDeltaModPMap, MvPolynomial.coeff_map, Int.coe_castRingHom,
        AddMonoidAlgebra.coeff_zero, Pi.zero_apply, Finsupp.zero_apply] using he
    let g : FreeDeltaRing σ := (AddMonoidAlgebra.coeffLinearEquiv ℤ).symm
      (((AddMonoidAlgebra.coeffLinearEquiv ℤ) x).mapRange (fun c ↦ c / (p : ℤ)) (by simp))
    have hxg : x = (p : FreeDeltaRing σ) * g := by
      apply MvPolynomial.ext
      intro d
      change x.coeff d = (MvPolynomial.C (p : ℤ) * g).coeff d
      rw [MvPolynomial.coeff_C_mul]
      change x.coeff d = (p : ℤ) * (x.coeff d / (p : ℤ))
      exact (Int.mul_ediv_cancel' (hcoeff d)).symm
    rw [hxg]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    change freeDeltaModPMap p σ (p : FreeDeltaRing σ) = 0
    rw [map_natCast, CharP.cast_eq_zero]

/-- 自由整数δ環のmod pと素数体係数多項式環の標準商同型。 -/
def freeDeltaModPEquiv :
    (FreeDeltaRing σ ⧸ Ideal.span {(p : FreeDeltaRing σ)}) ≃+*
      MvPolynomial (σ × ℕ) (ZMod p) :=
  (Ideal.quotEquivOfEq (freeDeltaModPMap_ker p σ).symm).trans
    (RingHom.quotientKerEquivOfSurjective (freeDeltaModPMap_surjective p σ))

/-- 標準商同型の代表元上の式。 -/
@[simp] theorem freeDeltaModPEquiv_mk (x : FreeDeltaRing σ) :
    freeDeltaModPEquiv p σ (Ideal.Quotient.mk _ x) = freeDeltaModPMap p σ x := rfl

/-- 標準商同型は自由δ環のFrobeniusのmod p式を素数体のFrobeniusへ移す。 -/
theorem freeDeltaModPEquiv_frobenius_mk (x : FreeDeltaRing σ) :
    freeDeltaModPEquiv p σ (Ideal.Quotient.mk _ (freeDeltaFrobenius p σ x)) =
      (freeDeltaModPEquiv p σ (Ideal.Quotient.mk _ x)) ^ p := by
  rw [freeDeltaFrobenius_mod_p, map_pow]

end SerrePositivity.BhattScholze

end FreeDeltaModP

/-! ## 素数体係数の多項式Frobeniusの忠実平坦性

FrobeniusがMathlibのexpand射と一致することを証明して、既構成の単項式基底を使う。
混標数の自由δ環のFrobeniusと完備化への接続は別工程。
-/

section PrimePolynomialFrobeniusFlat

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (σ : Type u)

/-- 素数体上の多項式Frobeniusは、係数を固定するexpand射そのもの。 -/
theorem primePolynomial_frobenius_eq_expand :
    frobenius (MvPolynomial σ (ZMod p)) p = (MvPolynomial.expand p).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change MvPolynomial.C c ^ p = MvPolynomial.expand p (MvPolynomial.C c)
    rw [MvPolynomial.expand_C, ← map_pow, ZMod.pow_card]
  · intro s
    change MvPolynomial.X s ^ p = MvPolynomial.expand p (MvPolynomial.X s)
    rw [MvPolynomial.expand_X]

/-- Frobenius作用を持つ標準ULift多項式環は自由。 -/
theorem primePolynomial_frobenius_moduleFree :
    letI : Algebra (MvPolynomial σ (ZMod p)) (PolynomialExpandTarget p σ (ZMod p)) :=
      (((ULift.ringEquiv : PolynomialExpandTarget p σ (ZMod p) ≃+*
        MvPolynomial σ (ZMod p)).symm.toRingHom).comp
          (frobenius (MvPolynomial σ (ZMod p)) p)).toAlgebra
    Module.Free (MvPolynomial σ (ZMod p)) (PolynomialExpandTarget p σ (ZMod p)) := by
  rw [primePolynomial_frobenius_eq_expand]
  exact polynomialExpand_moduleFree p σ (ZMod p) (Fact.out : p.Prime).pos

/-- Frobenius作用を持つ標準ULift多項式環は忠実平坦。 -/
theorem primePolynomial_frobenius_moduleFaithfullyFlat :
    letI : Algebra (MvPolynomial σ (ZMod p)) (PolynomialExpandTarget p σ (ZMod p)) :=
      (((ULift.ringEquiv : PolynomialExpandTarget p σ (ZMod p) ≃+*
        MvPolynomial σ (ZMod p)).symm.toRingHom).comp
          (frobenius (MvPolynomial σ (ZMod p)) p)).toAlgebra
    Module.FaithfullyFlat (MvPolynomial σ (ZMod p)) (PolynomialExpandTarget p σ (ZMod p)) := by
  rw [primePolynomial_frobenius_eq_expand]
  exact polynomialExpand_moduleFaithfullyFlat p σ (ZMod p) (Fact.out : p.Prime).pos

end SerrePositivity.BhattScholze

end PrimePolynomialFrobeniusFlat

/-! ## 自由整数δ環の実際のmod p Frobeniusの自由性

標準商同型と素数体の単項式基底を半線形同値で接続する。
混標数Frobeniusの完全平坦性をこの結果だけから推論しない。
-/

section FreeDeltaFrobeniusModPFlat

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (σ : Type u)
attribute [local instance] polynomialExpandAlgebra

/-- 自由δ環の剰余環にFrobenius作用を持たせるための標準ULift型。 -/
def FreeDeltaModPFrobeniusTarget := ULift.{0} (ModP (FreeDeltaRing σ) p)

instance freeDeltaModPFrobeniusTargetCommRing : CommRing (FreeDeltaModPFrobeniusTarget p σ) := by
  unfold FreeDeltaModPFrobeniusTarget
  infer_instance

/-- 自由δ環の実際の剰余Frobeniusによるスカラー作用。 -/
abbrev freeDeltaModPFrobeniusAlgebra : Algebra (ModP (FreeDeltaRing σ) p)
    (FreeDeltaModPFrobeniusTarget p σ) :=
  (((ULift.ringEquiv : FreeDeltaModPFrobeniusTarget p σ ≃+*
    ModP (FreeDeltaRing σ) p).symm.toRingHom).comp (modPMap p (freeDeltaFrobenius p σ))).toAlgebra

attribute [local instance] freeDeltaModPFrobeniusAlgebra

/-- 標準商同型は、実際の剰余Frobeniusを素数体のexpand射へ移す。 -/
theorem freeDeltaModPEquiv_modPMap_frobenius (a : ModP (FreeDeltaRing σ) p) :
    freeDeltaModPEquiv p σ (modPMap p (freeDeltaFrobenius p σ) a) =
      MvPolynomial.expand p (freeDeltaModPEquiv p σ a) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  change freeDeltaModPEquiv p σ (Ideal.Quotient.mk _ (freeDeltaFrobenius p σ x)) = _
  rw [freeDeltaModPEquiv_frobenius_mk]
  exact RingHom.congr_fun (primePolynomial_frobenius_eq_expand p (σ × ℕ)) _

/-- 標準商同型の順逆環射のMathlib逆対。 -/
abbrev freeDeltaModPInvPair :
    RingHomInvPair (freeDeltaModPEquiv p σ).toRingHom
      (freeDeltaModPEquiv p σ).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (freeDeltaModPEquiv p σ)

/-- 標準商同型の逆順環射のMathlib逆対。 -/
abbrev freeDeltaModPSymmInvPair :
    RingHomInvPair (freeDeltaModPEquiv p σ).symm.toRingHom
      (freeDeltaModPEquiv p σ).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (freeDeltaModPEquiv p σ)

attribute [local instance] freeDeltaModPInvPair freeDeltaModPSymmInvPair

/-- 実際の剰余Frobenius作用と、素数体上のexpand作用を結ぶ半線形同値。 -/
def freeDeltaModPFrobeniusEquiv :
    LinearEquiv (σ' := (freeDeltaModPEquiv p σ).symm.toRingHom)
      (freeDeltaModPEquiv p σ).toRingHom (FreeDeltaModPFrobeniusTarget p σ)
        (PolynomialExpandTarget p (σ × ℕ) (ZMod p)) where
  toFun x := ULift.up (freeDeltaModPEquiv p σ x.down)
  invFun x := ULift.up ((freeDeltaModPEquiv p σ).symm x.down)
  left_inv x := by
    apply ULift.ext
    exact (freeDeltaModPEquiv p σ).symm_apply_apply x.down
  right_inv x := by
    apply ULift.ext
    exact (freeDeltaModPEquiv p σ).apply_symm_apply x.down
  map_add' x y := by
    change ULift.up (freeDeltaModPEquiv p σ (x.down + y.down)) =
      ULift.up (freeDeltaModPEquiv p σ x.down + freeDeltaModPEquiv p σ y.down)
    rw [map_add]
  map_smul' a x := by
    change ULift.up (freeDeltaModPEquiv p σ
      (modPMap p (freeDeltaFrobenius p σ) a * x.down)) =
        ULift.up (MvPolynomial.expand p (freeDeltaModPEquiv p σ a) *
          freeDeltaModPEquiv p σ x.down)
    rw [map_mul, freeDeltaModPEquiv_modPMap_frobenius]

/-- 自由δ環の実際のmod p Frobenius作用の剰余環は自由加群。 -/
theorem freeDeltaModPFrobenius_moduleFree :
    Module.Free (ModP (FreeDeltaRing σ) p) (FreeDeltaModPFrobeniusTarget p σ) := by
  let := polynomialExpand_moduleFree p (σ × ℕ) (ZMod p) (Fact.out : p.Prime).pos
  exact Module.Free.of_equiv (freeDeltaModPFrobeniusEquiv p σ).symm

/-- 自由δ環の実際のmod p Frobenius作用の剰余環は忠実平坦（BS 著者版 Lemma 2.11 の Frobenius の mod p 忠実平坦性）。 -/
theorem freeDeltaModPFrobenius_moduleFaithfullyFlat :
    Module.FaithfullyFlat (ModP (FreeDeltaRing σ) p) (FreeDeltaModPFrobeniusTarget p σ) := by
  let : Nontrivial (ModP (FreeDeltaRing σ) p) :=
    (freeDeltaModPEquiv p σ).toRingHom.domain_nontrivial
  let : Nontrivial (FreeDeltaModPFrobeniusTarget p σ) := by
    unfold FreeDeltaModPFrobeniusTarget
    infer_instance
  let := freeDeltaModPFrobenius_moduleFree p σ
  infer_instance

end SerrePositivity.BhattScholze

end FreeDeltaFrobeniusModPFlat

/-! ## G3による自由整数δ環Frobeniusのp完全忠実平坦性 -/

section FreeDeltaFrobeniusCompletelyFlat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable (p : ℕ) [Fact p.Prime] (σ : Type u)
local notation "A₀" => FreeDeltaRing σ
local notation "Q₀" => ModP A₀ p

/-- 元の環とFrobeniusで作用される終域を区別するための標準ULift。 -/
def FreeDeltaFrobeniusTarget (_p : ℕ) (σ : Type u) := ULift.{0} (FreeDeltaRing σ)

instance freeDeltaFrobeniusTargetCommRing : CommRing (FreeDeltaFrobeniusTarget p σ) := by
  unfold FreeDeltaFrobeniusTarget
  infer_instance

local notation "B₀" => FreeDeltaFrobeniusTarget p σ
local notation "M₀" => FreeDeltaModPFrobeniusTarget p σ

/-- 実Frobeniusによる混標数の係数作用。 -/
abbrev freeDeltaFrobeniusAlgebra : Algebra A₀ B₀ :=
  (((ULift.ringEquiv : B₀ ≃+* A₀).symm.toRingHom).comp (freeDeltaFrobenius p σ)).toAlgebra

attribute [local instance] freeDeltaFrobeniusAlgebra freeDeltaModPFrobeniusAlgebra
attribute [local instance] adicQuotientAlgebra

omit [Fact p.Prime] in
/-- 混標数の係数作用は、元の実Frobeniusそのものである。 -/
theorem freeDeltaFrobeniusAlgebra_algebraMap (x : A₀) :
    (algebraMap A₀ B₀ x).down = freeDeltaFrobenius p σ x := rfl
local notation "I₀" => Ideal.span ({(p : A₀)} : Set A₀)
local notation "J₀" => Ideal.map (algebraMap A₀ B₀) I₀

omit [Fact p.Prime] in
/-- p主イデアルのFrobenius係数作用による拡大は、終域のp主イデアル。 -/
theorem freeDeltaFrobenius_pIdeal_map : J₀ = Ideal.span {(p : B₀)} := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

/-- 終域の実p剰余と既存mod p Frobenius終域の環同型。 -/
def freeDeltaFrobeniusResidueEquiv : B₀ ⧸ J₀ ≃+* M₀ :=
  (Ideal.quotEquivOfEq (freeDeltaFrobenius_pIdeal_map p σ)).trans
    ((Ideal.quotientEquiv I₀ (Ideal.span {(p : B₀)})
      (ULift.ringEquiv : B₀ ≃+* A₀).symm
      (by rw [Ideal.map_span, Set.image_singleton, map_natCast])).symm.trans
        (ULift.ringEquiv : M₀ ≃+* Q₀).symm)

omit [Fact p.Prime] in
/-- 剰余比較は元の標準商像をそのまま保つ。 -/
theorem freeDeltaFrobeniusResidueEquiv_mk (x : B₀) :
    freeDeltaFrobeniusResidueEquiv p σ (Ideal.Quotient.mk J₀ x) =
      ULift.up (Ideal.Quotient.mk I₀ x.down) := by
  rw [freeDeltaFrobeniusResidueEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingEquiv.trans_apply, Ideal.quotientEquiv_symm_mk]
  rfl

/-- 商比較は、Frobeniusを持つ正確なA/p作用について線形。 -/
def freeDeltaFrobeniusResidueLinearEquiv : (B₀ ⧸ J₀) ≃ₗ[Q₀] M₀ :=
  { (freeDeltaFrobeniusResidueEquiv p σ).toAddEquiv with
    map_smul' := by
      intro r x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      change freeDeltaFrobeniusResidueEquiv p σ
        (Ideal.Quotient.mk J₀ (algebraMap A₀ B₀ a * b)) =
          ULift.up (Ideal.Quotient.mk I₀ (freeDeltaFrobenius p σ a) *
            Ideal.Quotient.mk I₀ b.down)
      rw [freeDeltaFrobeniusResidueEquiv_mk]
      change ULift.up (Ideal.Quotient.mk I₀ (freeDeltaFrobenius p σ a * b.down)) = _
      rw [map_mul] }

/-- G3の通常商テンソルと既存mod p Frobenius加群との線形同値。 -/
def freeDeltaFrobeniusResidueTensorEquiv : (Q₀ ⊗[A₀] B₀) ≃ₗ[Q₀] M₀ :=
  (quotientTensorReductionEquiv I₀ B₀).trans
    ((adicReductionEquivAlgebraQuotient I₀ B₀).trans (freeDeltaFrobeniusResidueLinearEquiv p σ))

/-- 実Frobeniusで作用される終域のmod pテンソルは忠実平坦。 -/
theorem freeDeltaFrobenius_residueTensor_faithfullyFlat :
    Module.FaithfullyFlat Q₀ (Q₀ ⊗[A₀] B₀) := by
  have := freeDeltaModPFrobenius_moduleFaithfullyFlat p σ
  exact Module.FaithfullyFlat.of_linearEquiv Q₀ M₀ (freeDeltaFrobeniusResidueTensorEquiv p σ)

/-- pは実Frobeniusで作用される終域加群でも正則。 -/
theorem freeDeltaFrobeniusTarget_p_regular : IsSMulRegular B₀ (p : A₀) := by
  intro x y h
  apply ULift.ext
  apply freeDeltaRing_p_mul_injective p σ
  change algebraMap A₀ B₀ (p : A₀) * x = algebraMap A₀ B₀ (p : A₀) * y at h
  rw [map_natCast] at h
  exact congrArg ULift.down h

/-- G3による、自由整数δ環の実Frobeniusのp完全忠実平坦性（BS 著者版 Lemma 2.11 の Frobenius の p 完全忠実平坦性）。 -/
theorem freeDeltaFrobenius_isCompletelyFaithfullyFlat :
    IsCompletelyFaithfullyFlat I₀ B₀ :=
  isCompletelyFaithfullyFlat_principal_of_regular (p : A₀)
    (freeDeltaRing_p_mul_injective p σ) B₀ (freeDeltaFrobeniusTarget_p_regular p σ)
    (freeDeltaFrobenius_residueTensor_faithfullyFlat p σ)

end SerrePositivity.BhattScholze

end FreeDeltaFrobeniusCompletelyFlat

/-! ## 自由δ環Frobeniusの指定変数による実剰余射の忠実平坦性

対象はL/(p,z)→L/(p,φ(z))の通常射。完備化後の完全忠実平坦性は別工程。
-/

section FreeDeltaFrobeniusCoordinateResidueFlat

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (σ : Type u)
attribute [local instance] freeDeltaModPFrobeniusAlgebra
local notation "L₀" => FreeDeltaRing σ
local notation "R₀" => ModP L₀ p
local notation "B₀" => FreeDeltaModPFrobeniusTarget p σ

/-- 自由δ環の(p,x)商を、mod p環のx像の商に移す既存二重商同型。 -/
def freeDeltaPairModPEquiv (x : L₀) :
    (L₀ ⧸ Ideal.span {(p : L₀), x}) ≃+*
      (R₀ ⧸ Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : L₀)}) x}) :=
  (Ideal.quotEquivOfEq (Ideal.span_insert (p : L₀) {x})).trans
    ((DoubleQuot.quotQuotEquivQuotSup (Ideal.span {(p : L₀)}) (Ideal.span {x})).symm.trans
      (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])))

omit [Fact p.Prime] in
/-- 二重商比較は元の自由環の標準像と両立する。 -/
theorem freeDeltaPairModPEquiv_mk (x y : L₀) :
    freeDeltaPairModPEquiv p σ x (Ideal.Quotient.mk _ y) =
      Ideal.Quotient.mk _ (Ideal.Quotient.mk _ y) := by
  rw [freeDeltaPairModPEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingEquiv.trans_apply, DoubleQuot.quotQuotEquivQuotSup_symm_quotQuotMk]
  rfl

/-- 指定変数のmod p像の主イデアル。 -/
abbrev freeDeltaFrobeniusCoordinateIdeal (s : σ) : Ideal R₀ :=
  Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : L₀)}) (MvPolynomial.X (s, 0))}

/-- 実mod p Frobenius作用による指定変数イデアルの拡大。 -/
abbrev freeDeltaFrobeniusCoordinateTargetIdeal (s : σ) : Ideal B₀ :=
  (freeDeltaFrobeniusCoordinateIdeal p σ s).map (algebraMap R₀ B₀)

omit [Fact p.Prime] in
/-- 拡大イデアルはφ(z)の実mod p像で生成される。 -/
theorem freeDeltaFrobeniusCoordinateTargetIdeal_eq (s : σ) :
    freeDeltaFrobeniusCoordinateTargetIdeal p σ s =
      (Ideal.span {(Ideal.Quotient.mk (Ideal.span {(p : L₀)})
        (freeDeltaFrobenius p σ (MvPolynomial.X (s, 0))))}).map
        (ULift.ringEquiv : B₀ ≃+* R₀).symm.toRingHom := by
  rw [freeDeltaFrobeniusCoordinateTargetIdeal, freeDeltaFrobeniusCoordinateIdeal,
    Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]
  rfl

/-- 実通常商L/(p,φ(z))を忠実平坦基底変更の対象商へ移す同型。 -/
def freeDeltaFrobeniusCoordinateTargetEquiv (s : σ) :
    (L₀ ⧸ Ideal.span {(p : L₀), freeDeltaFrobenius p σ (MvPolynomial.X (s, 0))}) ≃+*
      (B₀ ⧸ freeDeltaFrobeniusCoordinateTargetIdeal p σ s) :=
  (freeDeltaPairModPEquiv p σ (freeDeltaFrobenius p σ (MvPolynomial.X (s, 0)))).trans
    (Ideal.quotientEquiv _ _ (ULift.ringEquiv : B₀ ≃+* R₀).symm
      (freeDeltaFrobeniusCoordinateTargetIdeal_eq p σ s))

omit [Fact p.Prime] in
/-- 対象商の比較は元の自由環の標準像を実剰余像へ送る。 -/
theorem freeDeltaFrobeniusCoordinateTargetEquiv_mk (s : σ) (y : L₀) :
    freeDeltaFrobeniusCoordinateTargetEquiv p σ s (Ideal.Quotient.mk _ y) =
      Ideal.Quotient.mk _ (ULift.up (Ideal.Quotient.mk (Ideal.span {(p : L₀)}) y)) := by
  rw [freeDeltaFrobeniusCoordinateTargetEquiv, RingEquiv.trans_apply,
    freeDeltaPairModPEquiv_mk, Ideal.quotientEquiv_mk]
  rfl

/-- 指定変数の商で基底変更した実mod p Frobenius作用の商環は忠実平坦。 -/
theorem freeDeltaFrobeniusCoordinateQuotient_moduleFaithfullyFlat (s : σ) :
    Module.FaithfullyFlat (R₀ ⧸ freeDeltaFrobeniusCoordinateIdeal p σ s)
      (B₀ ⧸ freeDeltaFrobeniusCoordinateTargetIdeal p σ s) := by
  let := freeDeltaModPFrobenius_moduleFaithfullyFlat p σ
  exact Module.FaithfullyFlat.of_linearEquiv _ _
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B₀
      (freeDeltaFrobeniusCoordinateIdeal p σ s)).toLinearEquiv

/-- L/(p,z)からL/(p,φ(z))への具体的な実剰余Frobenius射。 -/
def freeDeltaFrobeniusCoordinateResidueMap (s : σ) :
    (L₀ ⧸ Ideal.span {(p : L₀), MvPolynomial.X (s, 0)}) →+*
      (L₀ ⧸ Ideal.span {(p : L₀), freeDeltaFrobenius p σ (MvPolynomial.X (s, 0))}) :=
  (freeDeltaFrobeniusCoordinateTargetEquiv p σ s).symm.toRingHom.comp
    ((algebraMap (R₀ ⧸ freeDeltaFrobeniusCoordinateIdeal p σ s)
      (B₀ ⧸ freeDeltaFrobeniusCoordinateTargetIdeal p σ s)).comp
      (freeDeltaPairModPEquiv p σ (MvPolynomial.X (s, 0))).toRingHom)

omit [Fact p.Prime] in
/-- 実剰余射は元の自由環のFrobeniusによる標準商射そのもの。 -/
theorem freeDeltaFrobeniusCoordinateResidueMap_mk (s : σ) (y : L₀) :
    freeDeltaFrobeniusCoordinateResidueMap p σ s (Ideal.Quotient.mk _ y) =
      Ideal.Quotient.mk _ (freeDeltaFrobenius p σ y) := by
  apply (freeDeltaFrobeniusCoordinateTargetEquiv p σ s).injective
  change (freeDeltaFrobeniusCoordinateTargetEquiv p σ s)
    ((freeDeltaFrobeniusCoordinateTargetEquiv p σ s).symm _) = _
  rw [RingEquiv.apply_symm_apply]
  change algebraMap (R₀ ⧸ freeDeltaFrobeniusCoordinateIdeal p σ s)
    (B₀ ⧸ freeDeltaFrobeniusCoordinateTargetIdeal p σ s)
    (freeDeltaPairModPEquiv p σ (MvPolynomial.X (s, 0)) (Ideal.Quotient.mk _ y)) = _
  rw [freeDeltaPairModPEquiv_mk, freeDeltaFrobeniusCoordinateTargetEquiv_mk]
  rfl

/-- 実通常射L/(p,z)→L/(p,φ(z))は忠実平坦。 -/
theorem freeDeltaFrobeniusCoordinateResidueMap_faithfullyFlat (s : σ) :
    (freeDeltaFrobeniusCoordinateResidueMap p σ s).FaithfullyFlat := by
  have hb : (algebraMap (R₀ ⧸ freeDeltaFrobeniusCoordinateIdeal p σ s)
      (B₀ ⧸ freeDeltaFrobeniusCoordinateTargetIdeal p σ s)).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr
      (freeDeltaFrobeniusCoordinateQuotient_moduleFaithfullyFlat p σ s)
  have hs := RingHom.FaithfullyFlat.of_bijective
    (f := (freeDeltaPairModPEquiv p σ (MvPolynomial.X (s, 0))).toRingHom)
    (freeDeltaPairModPEquiv p σ (MvPolynomial.X (s, 0))).bijective
  have ht := RingHom.FaithfullyFlat.of_bijective
    (f := (freeDeltaFrobeniusCoordinateTargetEquiv p σ s).symm.toRingHom)
    (freeDeltaFrobeniusCoordinateTargetEquiv p σ s).symm.bijective
  exact RingHom.FaithfullyFlat.stableUnderComposition _ _
    (RingHom.FaithfullyFlat.stableUnderComposition _ _ hs hb) ht

/-- 指定変数のFrobeniusのmod p像はzのp乗。 -/
theorem freeDeltaFrobeniusCoordinate_mod_p (s : σ) :
    Ideal.Quotient.mk (Ideal.span {(p : L₀)})
      (freeDeltaFrobenius p σ (MvPolynomial.X (s, 0))) =
      Ideal.Quotient.mk (Ideal.span {(p : L₀)}) (MvPolynomial.X (s, 0)) ^ p :=
  freeDeltaFrobenius_mod_p p σ _

end SerrePositivity.BhattScholze

end FreeDeltaFrobeniusCoordinateResidueFlat

/-! ## 自由δ Frobeniusの指定変数に沿う正則対

自由整数δ環に限る入力。一般perfectoid環のp正則性は要求しない。
通常の正則対と、完備化後の完全忠実平坦性は区別する。
-/

section FreeDeltaFrobeniusCoordinateRegular

set_option backward.isDefEq.respectTransparency false
open scoped Pointwise
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (σ : Type u)
local notation "L₀" => FreeDeltaRing σ
local notation "R₀" => ModP L₀ p

/-- 自由整数δ環の指定変数のmod p像は正則。 -/
theorem freeDeltaCoordinate_modP_isSMulRegular (s : σ) :
    IsSMulRegular R₀ (Ideal.Quotient.mk (Ideal.span {(p : L₀)})
      (MvPolynomial.X (s, 0))) := by
  intro x y hxy
  apply (freeDeltaModPEquiv p σ).injective
  apply (MvPolynomial.isRegular_X (R := ZMod p) (n := (s, 0))).left
  have h := congrArg (freeDeltaModPEquiv p σ) hxy
  simpa only [smul_eq_mul, map_mul, freeDeltaModPEquiv_mk,
    freeDeltaModPMap, MvPolynomial.map_X] using h

/-- 自由整数δ環のφ(z)のmod p像も正則。 -/
theorem freeDeltaFrobeniusCoordinate_modP_isSMulRegular (s : σ) :
    IsSMulRegular R₀ (Ideal.Quotient.mk (Ideal.span {(p : L₀)})
      (freeDeltaFrobenius p σ (MvPolynomial.X (s, 0)))) := by
  rw [freeDeltaFrobeniusCoordinate_mod_p]
  exact (freeDeltaCoordinate_modP_isSMulRegular p σ s).pow p

/-- 源の指定変数とpは自由整数δ環上の弱正則対。 -/
theorem freeDeltaCoordinate_pair_isWeaklyRegular (s : σ) :
    RingTheory.Sequence.IsWeaklyRegular L₀ [(p : L₀), MvPolynomial.X (s, 0)] := by
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  refine ⟨freeDeltaRing_p_mul_injective p σ, ?_⟩
  change IsSMulRegular (L₀ ⧸ ((p : L₀) • ⊤ : Submodule L₀ L₀)) _
  let e := Submodule.quotEquivOfEq
    ((p : L₀) • (⊤ : Submodule L₀ L₀))
    (Ideal.span {(p : L₀)} : Submodule L₀ L₀)
    (by rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top])
  apply (e.isSMulRegular_congr _).mpr
  exact (isSMulRegular_map (Ideal.Quotient.mk _) (fun _ ↦ rfl)).mp
    (freeDeltaCoordinate_modP_isSMulRegular p σ s)

/-- 対象のφ(z)とpも自由整数δ環上の弱正則対。 -/
theorem freeDeltaFrobeniusCoordinate_pair_isWeaklyRegular (s : σ) :
    RingTheory.Sequence.IsWeaklyRegular L₀
      [(p : L₀), freeDeltaFrobenius p σ (MvPolynomial.X (s, 0))] := by
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  refine ⟨freeDeltaRing_p_mul_injective p σ, ?_⟩
  change IsSMulRegular (L₀ ⧸ ((p : L₀) • ⊤ : Submodule L₀ L₀)) _
  let e := Submodule.quotEquivOfEq
    ((p : L₀) • (⊤ : Submodule L₀ L₀))
    (Ideal.span {(p : L₀)} : Submodule L₀ L₀)
    (by rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top])
  apply (e.isSMulRegular_congr _).mpr
  exact (isSMulRegular_map (Ideal.Quotient.mk _) (fun _ ↦ rfl)).mp
    (freeDeltaFrobeniusCoordinate_modP_isSMulRegular p σ s)

/-- 源の実正則対のKoszul複体は通常商の分解。 -/
theorem freeDeltaCoordinate_pair_isKoszulResolution (s : σ) :
    SerrePositivity.IsKoszulResolution
      (fun i : Fin 2 ↦ if i = 0 then (p : L₀) else MvPolynomial.X (s, 0)) := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  simpa [List.ofFn_succ] using freeDeltaCoordinate_pair_isWeaklyRegular p σ s

/-- 対象の実正則対のKoszul複体も通常商の分解。 -/
theorem freeDeltaFrobeniusCoordinate_pair_isKoszulResolution (s : σ) :
    SerrePositivity.IsKoszulResolution
      (fun i : Fin 2 ↦ if i = 0 then (p : L₀)
        else freeDeltaFrobenius p σ (MvPolynomial.X (s, 0))) := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  simpa [List.ofFn_succ] using freeDeltaFrobeniusCoordinate_pair_isWeaklyRegular p σ s

/-- 実Frobeniusに沿うL/(p,z)の全高次Torは零。
任意の(p,z)零化加群に対する完全平坦性の判定とは区別する。 -/
theorem freeDeltaFrobeniusCoordinate_residue_torAlg_subsingleton
    (s : σ) (i : ℕ) (hi : 0 < i) :
    Subsingleton (SerrePositivity.TorAlg (freeDeltaFrobenius p σ) i
      (L₀ ⧸ Ideal.span {(p : L₀), MvPolynomial.X (s, 0)})) := by
  let g : Fin 2 → L₀ := fun j ↦ if j = 0 then p else MvPolynomial.X (s, 0)
  have hg : freeDeltaFrobenius p σ ∘ g =
      (fun j : Fin 2 ↦ if j = 0 then (p : L₀)
        else freeDeltaFrobenius p σ (MvPolynomial.X (s, 0))) := by
    funext j
    simp only [Function.comp_apply, g]
    split <;> simp_all
  have hz : CategoryTheory.Limits.IsZero
      ((SerrePositivity.koszulComplex (freeDeltaFrobenius p σ ∘ g)).homology (-(i : ℤ))) := by
    rw [hg]
    exact (freeDeltaFrobeniusCoordinate_pair_isKoszulResolution p σ s).isZero _ (by omega)
  have : Subsingleton (SerrePositivity.koszulHomologySelf
      (freeDeltaFrobenius p σ ∘ g) i) := ModuleCat.subsingleton_of_isZero hz
  have ht : Subsingleton (SerrePositivity.TorAlg (freeDeltaFrobenius p σ) i
      (L₀ ⧸ Ideal.span (Set.range g))) :=
    (SerrePositivity.torAlgKoszulEquiv (freeDeltaFrobenius p σ) g
      (freeDeltaCoordinate_pair_isKoszulResolution p σ s) i).injective.subsingleton
  have hr : Set.range g = {(p : L₀), MvPolynomial.X (s, 0)} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩
      fin_cases j <;> simp [g]
    · rintro (rfl | rfl)
      · exact ⟨0, by simp [g]⟩
      · exact ⟨1, by simp [g]⟩
  rw [hr] at ht
  exact ht

end SerrePositivity.BhattScholze

end FreeDeltaFrobeniusCoordinateRegular

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Lemma 2.11" (partial := special) "係数は Z（原典は Z_(p)）、多項式環としての記述と普遍性。Frobenius は mod p で自由・忠実平坦、p 完全忠実平坦まで（「本当の忠実平坦性は述べない」）。Q{x} の主張は未 ／ DOC1 照合：ok 4 件"] _root_.SerrePositivity.BhattScholze.freeDeltaFrobenius_isCompletelyFaithfullyFlat
attribute [cite BS19 "Lemma 2.11" (partial := special) "係数は Z（原典は Z_(p)）、多項式環としての記述と普遍性。Frobenius は mod p で自由・忠実平坦、p 完全忠実平坦まで（「本当の忠実平坦性は述べない」）。Q{x} の主張は未 ／ DOC1 照合：ok 4 件"] _root_.SerrePositivity.BhattScholze.freeDeltaModPFrobenius_moduleFaithfullyFlat
