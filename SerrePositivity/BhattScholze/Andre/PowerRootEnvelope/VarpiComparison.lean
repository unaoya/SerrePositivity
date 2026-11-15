module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Completion
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.CompletionPrism
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Unconditional.FrobeniusPD
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.PerfectionFaithful
public import SerrePositivity.HomologicalAlgebra.TorAlgebraAcyclicBaseChange
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Criterion
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.PowerTorsion
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.VarpiPD
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Unconditional.Residue
public import Mathlib.RingTheory.TensorProduct.Quotient
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Unconditional.Source

/-!
# p と ϖ の照合（BS 著者版 Remark 7.15）

## 概要
p と ϖ の完全平坦性、pd 表示環の係数テンソル底変換とそれが分冪射であること、R/p から R/ϖ への pd 底変換、正則性を足さない係数テンソルの分冪構造、二元完全平坦性、具体的候補・Hodge–Tate 係数の照合。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`PowerRootEnvelope/Audit`、`PowerRootEnvelope/Initiality`、`Variants/MonicRootedExtension`。
-/

universe u

/-! ## 元の無限根モニック実完備化の二元完全平坦性

## 概要

元の実完備化 H は、元の完全 prism の係数作用について (p,d) 完全平坦。
BS 著者版 Remark 7.15（著者版 p.62）の δ 完全化に渡す導来剰余の計算。

## 方針

自然な H/d の係数作用と標準主環商の作用を照合し、d の正則性から p 完全平坦性を戻す。

## 規約

元の実 H⁰ と標準係数射を保持する。hpR を仮定せず、モニック性・正次数を要求する。

## 使われ方

元の H の導来 (p,d) 剰余を δ 完全化の一般剰余判定へ渡す。
-/

@[expose] public noncomputable section PowerRootCompletionPairFlat

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
open _root_.SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (f : Polynomial A) (hf : f.Monic) (hdeg : 0 < f.natDegree)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "uL" => pdCompletionUnit L p (jL dP)
local notation "T" => H ⧸ Ideal.span {uL (jL dP)}
local notation "R" => A ⧸ W.ideal
local notation "v" => perfectPrismVarpi W hW
local notation "φ" => powerRootPrismMonicHodgeTateBaseMap W hW f



local notation "DL" => deltaAdjoinDivisionStructure E dP a
local notation "DH" => deltaPDCompletionStructure DL (jL dP)


include hf hdeg in
/-- 概要：元の無限根モニック実完備化は (p,d) 完全平坦。
方針：分母正則性と標準作用に移した H/d の p 完全平坦性を一般判定へ渡す。
規約：元の A 係数作用と実 H⁰ を用いる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完全 δ 化の導来剰余入力。 -/
theorem powerRootPrismMonicCompletion_pair_completelyFlat_of_unconditional :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicCompletionAlgebra W hW f
    IsCompletelyFlat (Ideal.span {(p : A), W.generator}) H := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicCompletionAlgebra W hW f
  have hreg : IsSMulRegular H (algebraMap A H W.generator) :=
    powerRootPrismMonicRaw_pdCompletion_generator_regular_of_unconditional W hW f hf hdeg
  have hred : let := principalAdicQuotientAlgebra W.generator H
      IsCompletelyFlat (Ideal.span {(p : A ⧸ Ideal.span {W.generator})})
        (H ⧸ Ideal.span {algebraMap A H W.generator}) := by
    rw [← powerRootPrismMonicHodgeTateAlgebra_eq_principal W hW f]
    exact (powerRootPrismMonicHodgeTate_prime_completelyFaithfullyFlat_of_unconditional W hW f hf hdeg).1
  apply completelyFlat_pair_algebra_of_regular_reduction (p : A) W.generator
    W.generator_regular H hreg
  simpa only [map_natCast] using hred

include hf hdeg in
/-- 概要：元の実完備化の (p,d) 標準底変換の高次 Tor は零。
方針：二元完全平坦性を標準剰余係数加群へ適用する。
規約：標準係数作用を持つ加群そのものを使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の導来剰余の離散性。 -/
theorem powerRootPrismMonicCompletion_pair_scalarExtensionTorVanishing_of_unconditional :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicCompletionAlgebra W hW f
    scalarExtensionTorVanishing (Ideal.Quotient.mk (Ideal.span {(p : A), W.generator}))
      (baseChangeScalarModule (powerRootPrismMonicCompletionBaseMap W hW f)) := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicCompletionAlgebra W hW f
  apply scalarExtensionTorVanishing_of_completelyFlat
  exact isCompletelyFlat_of_linearEquiv _
    (powerRootPrismMonicCompletionScalarEquiv W hW f).symm
    (powerRootPrismMonicCompletion_pair_completelyFlat_of_unconditional W hW f hf hdeg)

include hf hdeg in
/-- 概要：元の実完備化の導来 (p,d) 剰余は非零次数で消える。
方針：高次 Tor の消滅から標準増大同型を作り、単項複体のホモロジーを使う。
規約：標準係数射で制限した実加群の導来底変換を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の δ 完全化の剰余計算。 -/
theorem powerRootPrismMonicCompletion_pair_reduction_homology_isZero_of_unconditional
    (i : ℤ) (hi : i ≠ 0) :
    let := pdCompletionCommRing L p (jL dP)
    IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat (A ⧸ Ideal.span {(p : A), W.generator})) i).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk
        (Ideal.span {(p : A), W.generator}))).obj
        (boundedAboveDerivedSingleFunctor.obj
          (baseChangeScalarModule (powerRootPrismMonicCompletionBaseMap W hW f)))).obj) := by
  let := pdCompletionCommRing L p (jL dP)
  let q := Ideal.Quotient.mk (Ideal.span {(p : A), W.generator})
  let M := baseChangeScalarModule (powerRootPrismMonicCompletionBaseMap W hW f)
  let e := boundedAboveDerivedBaseChangeModuleAugmentationIso q M
    (powerRootPrismMonicCompletion_pair_scalarExtensionTorVanishing_of_unconditional W hW f hf hdeg)
  exact (derivedSingleHomology_isZero ((ModuleCat.extendScalars q).obj M) i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat _) i).mapIso
      (DerivedCategory.Minus.ι.mapIso e))

include hf hdeg in
/-- 概要：元の実完備化の標準二元剰余は忠実平坦。
方針：自然な主環商作用を照合し、二段剰余の一般判定を適用する。
規約：元の標準係数射で制限した実加群を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の導来二元剰余 H⁰。 -/
theorem powerRootPrismMonicCompletion_pair_scalarExtension_faithfullyFlat_of_unconditional :
    let := pdCompletionCommRing L p (jL dP)
    Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), W.generator})
      ((ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {(p : A), W.generator}))).obj
        (baseChangeScalarModule (powerRootPrismMonicCompletionBaseMap W hW f))) := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicCompletionAlgebra W hW f
  let qd := Ideal.Quotient.mk (Ideal.span {W.generator})
  have hred : let := principalAdicQuotientAlgebra W.generator H
      IsCompletelyFaithfullyFlat (Ideal.span {(p : A ⧸ Ideal.span {W.generator})})
        (H ⧸ Ideal.span {algebraMap A H W.generator}) := by
    rw [← powerRootPrismMonicHodgeTateAlgebra_eq_principal W hW f]
    exact powerRootPrismMonicHodgeTate_prime_completelyFaithfullyFlat_of_unconditional W hW f hf hdeg
  let := principalAdicQuotientAlgebra W.generator H
  let e := (ModuleCat.extendScalars qd).mapIso
      (powerRootPrismMonicCompletionScalarEquiv W hW f).toModuleIso ≪≫
    (principalScalarExtensionAlgebraQuotientEquiv W.generator H).toModuleIso
  apply pairScalarExtension_faithfullyFlat_of_principal_reduction
  apply isCompletelyFaithfullyFlat_of_linearEquiv _ e.toLinearEquiv.symm
  simpa only [map_natCast] using hred

include hf hdeg in
/-- 概要：元の実完備化の導来二元剰余 H⁰ は忠実平坦。
方針：標準スカラー拡大と実導来底変換 H⁰ の自然な同型で移す。
規約：同じ基底商と標準係数射を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完全 δ 化の剰余判定。 -/
theorem powerRootPrismMonicCompletion_pair_reductionH0_faithfullyFlat_of_unconditional :
    let := pdCompletionCommRing L p (jL dP)
    Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), W.generator})
      ((DerivedCategory.homologyFunctor
        (ModuleCat (A ⧸ Ideal.span {(p : A), W.generator})) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk
          (Ideal.span {(p : A), W.generator}))).obj
          (boundedAboveDerivedSingleFunctor.obj
            (baseChangeScalarModule (powerRootPrismMonicCompletionBaseMap W hW f)))).obj) := by
  let := pdCompletionCommRing L p (jL dP)
  let q := Ideal.Quotient.mk (Ideal.span {(p : A), W.generator})
  let M := baseChangeScalarModule (powerRootPrismMonicCompletionBaseMap W hW f)
  let := powerRootPrismMonicCompletion_pair_scalarExtension_faithfullyFlat_of_unconditional W hW f hf hdeg
  exact Module.FaithfullyFlat.of_linearEquiv _ ((ModuleCat.extendScalars q).obj M)
    ((boundedAboveDerivedBaseChangeModuleH0Iso q).app M).toLinearEquiv

end SerrePositivity.BhattScholze.Andre

end PowerRootCompletionPairFlat

/-! ## BS 著者版 Remark 7.15（著者版 p.62）：p と ϖ の完全平坦性の照合

## 概要
主イデアル (ϖ^n)=(c) の下で c 完全平坦性と ϖ 完全平坦性を比較する。
通常の商による逆向きの判定には、基底と加群上の ϖ 正則性を明示する。

## 方針
冪ねじれ加群の Tor 消滅と忠実性の既存 API を用いる。

## 規約
任意の可換環で成り立つ形を公開する。原典では c=p、n=p、ϖ^p=p·単元を用いる。
通常商の平坦性だけから高次 Tor 消滅を推論しない。

## 使われ方
R/ϖ の pd 計算と候補の p 完全忠実平坦性を結ぶ。
-/

@[expose] public noncomputable section Flatness

namespace SerrePositivity.BhattScholze.Andre.VarpiComparison
open _root_.TensorProduct
open scoped _root_.TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [CommRing R]

/-- 概要：ϖ の正冪が c と単元の積なら、同じ主イデアルを生成する。
方針：単元倍で主イデアルが不変であることを使う。
規約：任意の環と指数に成立する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の ϖ^p=u·p から一般比較への入力。 -/
theorem span_power_eq_of_unit (v c : R) (n : ℕ) (u : Rˣ)
    (hpow : v ^ n = (u : R) * c) : Ideal.span {v ^ n} = Ideal.span {c} := by
  rw [hpow, mul_comm]
  exact Ideal.span_singleton_mul_right_unit u.isUnit c

/-- 概要：試験イデアルを大きくすると完全平坦性は保存される。
方針：消滅条件を包含で制限する。規約：正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の p から ϖ への方向。 -/
theorem completelyFlat_of_le (I J : Ideal R) (hIJ : I ≤ J)
    (M : Type u) [AddCommGroup M] [Module R M] (hM : IsCompletelyFlat I M) :
    IsCompletelyFlat J M := by
  intro N _ _ hN
  exact hM N (fun r hr => hN r (hIJ hr))

/-- 概要：同じ主イデアルを生成する正冪は完全平坦性を変えない。
方針：試験イデアルの包含と既存の有限冪デヴィサージュを使う。
規約：基底・加群の正則性も完備性も不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の (ϖ^p)=(p)。 -/
theorem completelyFlat_iff (v c : R) (n : ℕ) (hn : 0 < n)
    (hspan : Ideal.span {v ^ n} = Ideal.span {c})
    (M : Type u) [AddCommGroup M] [Module R M] :
    IsCompletelyFlat (Ideal.span {c}) M ↔ IsCompletelyFlat (Ideal.span {v}) M := by
  constructor
  · intro hM
    apply completelyFlat_of_le _ _ ?_ M hM
    rw [← hspan]
    exact Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self v (Nat.ne_of_gt hn))
  · intro hM
    simpa only [hspan] using isCompletelyFlat_principal_power v M hM n

/-- 概要：c 完全忠実平坦な加群の通常の ϖ 還元は忠実平坦。
方針：c で消える試験加群の零性検出を ϖ 剰余テンソルへ移す。
規約：(ϖ^n)=(c)、n>0 のみを要し、加群の正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の原典の通常忠実平坦性。 -/
theorem residueTensor_faithfullyFlat (v c : R) (n : ℕ) (hn : 0 < n)
    (hspan : Ideal.span {v ^ n} = Ideal.span {c})
    (M : Type u) [AddCommGroup M] [Module R M]
    (hM : IsCompletelyFaithfullyFlat (Ideal.span {c}) M) :
    Module.FaithfullyFlat (R ⧸ Ideal.span {v}) ((R ⧸ Ideal.span {v}) ⊗[R] M) := by
  apply (Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality _ _).mpr
  refine ⟨flat_residueTensor_of_completelyFlat _ M
    ((completelyFlat_iff v c n hn hspan M).mp hM.1), ?_⟩
  intro N _ _ hTensor
  let I := Ideal.span {v}
  let _ : Module R N := Module.compHom N (Ideal.Quotient.mk I)
  let _ : IsScalarTower R (R ⧸ I) N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have : Subsingleton (N ⊗[R ⧸ I] ((R ⧸ I) ⊗[R] M)) := hTensor
  let e := AlgebraTensorModule.cancelBaseChange R (R ⧸ I) (R ⧸ I) N M
  have hTN : Subsingleton (N ⊗[R] M) := e.surjective.subsingleton
  have hc : c ∈ I := by
    have hle : Ideal.span {c} ≤ I := by
      rw [← hspan]
      exact Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self v (Nat.ne_of_gt hn))
    exact hle (Ideal.mem_span_singleton_self _)
  have hN : ∀ x : N, c ^ 1 • x = 0 := by
    intro x
    change Ideal.Quotient.mk I (c ^ 1) • x = 0
    rw [pow_one, Ideal.Quotient.eq_zero_iff_mem.mpr hc, zero_smul]
  have := hM.2
  exact subsingleton_of_power_torsion_of_residueTensor c M 1 N hN hTN

/-- 概要：同じ主イデアルを生成する正冪は完全忠実平坦性を変えない。
方針：ϖ 還元の忠実性と各正冪の忠実性を既存 API から得る。
規約：任意の加群に成立し、正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の p と ϖ の係数表記の照合。 -/
theorem completelyFaithfullyFlat_iff (v c : R) (n : ℕ) (hn : 0 < n)
    (hspan : Ideal.span {v ^ n} = Ideal.span {c})
    (M : Type u) [AddCommGroup M] [Module R M] :
    IsCompletelyFaithfullyFlat (Ideal.span {c}) M ↔
      IsCompletelyFaithfullyFlat (Ideal.span {v}) M := by
  constructor
  · intro hM
    exact ⟨(completelyFlat_iff v c n hn hspan M).mp hM.1,
      residueTensor_faithfullyFlat v c n hn hspan M hM⟩
  · intro hM
    refine ⟨(completelyFlat_iff v c n hn hspan M).mpr hM.1, ?_⟩
    rw [← hspan]
    exact faithfullyFlat_power_residueTensor_of_completelyFaithfullyFlat v M hM n

/-- 概要：基底と M 上で ϖ が正則なら、c 完全平坦性は通常商の平坦性と同値。
方針：主元の正則性判定と冪による完全平坦性の不変性を組み合わせる。
規約：M 上の正則性を落とすと M=R/(ϖ) が反例となる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の pd 計算による判定。 -/
theorem completelyFlat_iff_flat_reduction (v c : R) (n : ℕ) (hn : 0 < n)
    (hspan : Ideal.span {v ^ n} = Ideal.span {c}) (hv : IsSMulRegular R v)
    (M : Type u) [AddCommGroup M] [Module R M] (hMv : IsSMulRegular M v) :
    IsCompletelyFlat (Ideal.span {c}) M ↔
      Module.Flat (R ⧸ Ideal.span {v}) (AdicReduction (Ideal.span {v}) M) := by
  rw [completelyFlat_iff v c n hn hspan M]
  constructor
  · intro hM
    have := flat_residueTensor_of_completelyFlat _ M hM
    exact Module.Flat.of_linearEquiv (quotientTensorReductionEquiv (Ideal.span {v}) M).symm
  · intro hM
    have := hM
    exact isCompletelyFlat_principal_of_regular v hv M hMv
      (Module.Flat.of_linearEquiv (quotientTensorReductionEquiv (Ideal.span {v}) M))

/-- 概要：基底と M 上で ϖ が正則なら、c 完全忠実平坦性は通常商の忠実平坦性と同値。
方針：正則主元の忠実平坦判定を完全忠実平坦性の冪不変性で移す。
規約：通常商と導来商を正則性なしに同一視しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の原典の忠実平坦性の説明。 -/
theorem completelyFaithfullyFlat_iff_faithfullyFlat_reduction
    (v c : R) (n : ℕ) (hn : 0 < n)
    (hspan : Ideal.span {v ^ n} = Ideal.span {c}) (hv : IsSMulRegular R v)
    (M : Type u) [AddCommGroup M] [Module R M] (hMv : IsSMulRegular M v) :
    IsCompletelyFaithfullyFlat (Ideal.span {c}) M ↔
      Module.FaithfullyFlat (R ⧸ Ideal.span {v}) (AdicReduction (Ideal.span {v}) M) := by
  rw [completelyFaithfullyFlat_iff v c n hn hspan M]
  constructor
  · intro hM
    have := hM.2
    exact Module.FaithfullyFlat.of_linearEquiv _ _
      (quotientTensorReductionEquiv (Ideal.span {v}) M).symm
  · intro hM
    have := hM
    exact isCompletelyFaithfullyFlat_principal_of_regular v hv M hMv
      (Module.FaithfullyFlat.of_linearEquiv _ _ (quotientTensorReductionEquiv (Ideal.span {v}) M))

attribute [local instance] adicQuotientAlgebra

/-- 概要：c 完全忠実平坦な R 代数の ϖ 商は R/ϖ 上忠実平坦。
方針：通常剰余テンソルと像イデアル商の標準同型を使う。
規約：代数の正則性を追加しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の候補 T の通常剰余。 -/
theorem algebraQuotient_faithfullyFlat (v c : R) (n : ℕ) (hn : 0 < n)
    (hspan : Ideal.span {v ^ n} = Ideal.span {c})
    (T : Type u) [CommRing T] [Algebra R T]
    (hT : IsCompletelyFaithfullyFlat (Ideal.span {c}) T) :
    Module.FaithfullyFlat (R ⧸ Ideal.span {v})
      (T ⧸ (Ideal.span {v}).map (algebraMap R T)) := by
  have := residueTensor_faithfullyFlat v c n hn hspan T hT
  exact Module.FaithfullyFlat.of_linearEquiv _ _
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor T (Ideal.span {v})).toLinearEquiv

end SerrePositivity.BhattScholze.Andre.VarpiComparison

end Flatness

/-! ## BS 著者版 Remark 7.15（著者版 p.62）の pd 表示環の係数テンソル底変換
旧ファイルは `Andre/Remark715/VarpiComparison/PDBaseChange.lean`。

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

@[expose] public noncomputable section PDBaseChange

namespace SerrePositivity.BhattScholze.Andre.VarpiComparison
open scoped _root_.TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2048

section General
variable (S : Type u) [CommRing S] (p : ℕ) (hp : 0 < p) (c : S) (f : Polynomial S)
local notation "N" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial S p hp
local notation "z" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap S p hp f
local notation "D" => PrincipalDPPresentation N z
local notation "Q" => S ⧸ Ideal.span {(c : S)}
local notation "NQ" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial Q p hp
local notation "zQ" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap Q p hp (f.map (Ideal.Quotient.mk _))

/-- 概要：無限根環の pd 表示を係数商へテンソルすると、同じ入力の pd 表示となる。
方針：通常テンソル商の同型と既存の二重商交換を合成する。
規約：任意の係数環・入力で成立する台環同型である。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の R/p から R/ϖ への底変換。 -/
def powerRootPDTensorQuotientEquiv : Q ⊗[S] D ≃+* PrincipalDPPresentation NQ zQ :=
  ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor D (Ideal.span {c})).symm.toRingEquiv.trans
    (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton]))).trans
      (principalDPReducedCoefficientEquiv (algebraMap S N c) z (algebraMap S D c)
        (IsScalarTower.algebraMap_apply S N D c)
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootCoefficientQuotientEquiv S p hp c) zQ (by
          rw [_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootCoefficientQuotientEquiv_mk, _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootCoefficientQuotientMap_baseMap]))

/-- 概要：係数テンソル比較はすべての標準分冪生成元を保つ。
方針：商テンソルの代表元公式と既存の生成元公式を使う。
規約：次数零も含む。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の pd 構造の係数変更。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の一般テンソル比較を R/p へ適用する係数同定。 -/
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
local notation "Nv" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial Rv p hp
local notation "barr" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW})) (Ideal.Quotient.mk W.ideal)
local notation "zv" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap Rv p hp (f.map barr)
local notation "Dv" => PrincipalDPPresentation Nv zv

/-- 概要：原典の R/ϖ に A/p の自然な係数作用を入れる。
方針：(A/p)/(x)≃R/ϖ と標準商射を合成する。
規約：x=φ⁻¹(d) mod p であり、R/p と A/p を混同しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実係数テンソル。 -/
@[instance_reducible] def varpiCoefficientAlgebra : Algebra R₀ Rv :=
  (((perfectPrismVarpiQuotientEquiv W hW).symm.toRingHom).comp
    (Ideal.Quotient.mk (Ideal.span {x}))).toAlgebra

/-- 概要：既存の係数商同型は A/p 代数同型である。
方針：自然な係数作用の定義を使う。
規約：順方向は (A/p)/(x) から R/ϖ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）のテンソル因子の比較。 -/
def varpiCoefficientAlgEquiv :
    let := varpiCoefficientAlgebra W hW
    Q ≃ₐ[R₀] Rv := by
  let := varpiCoefficientAlgebra W hW
  exact { (perfectPrismVarpiQuotientEquiv W hW).symm with commutes' := fun _ => rfl }

/-- 概要：実装の A/p 係数 pd 包を R/ϖ へ底変換すると原典の同じ pd 表示環となる。
方針：係数商代数同型でテンソル因子を移し、既存の pd 係数商比較へ合成する。
規約：ϖ^p=p·単元による R/ϖ の係数作用を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の二つの係数表記の実同型。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の自然な pd 底変換射の照合。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の pd 包としての構造照合。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の pd 包の係数底変換。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の pd 包としての底変換の具体的計算。 -/
theorem perfectPrismPDTensorVarpiDividedPowers_generator
    (hf : f.Monic) (i : ℕ) :
    let := varpiCoefficientAlgebra W hW
    (perfectPrismPDTensorVarpiDividedPowers W hW f hf).dpow i
      (1 ⊗ₜ[R₀] algebraMap (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial R₀ p hp) D (powerRootCoefficientPDInput p f)) =
        1 ⊗ₜ[R₀] principalDPGenerator (powerRootCoefficientPDInput p f) i := by
  let := varpiCoefficientAlgebra W hW
  let e := perfectPrismPDTensorVarpiEquiv W hW f
  change e.symm ((perfectPrismVarpiNativeDividedPowers_of_unconditional W hW f hf).dpow i
    (e (1 ⊗ₜ[R₀] algebraMap (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial R₀ p hp) D
      (powerRootCoefficientPDInput p f)))) = _
  have hInput : e (1 ⊗ₜ[R₀] algebraMap (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial R₀ p hp) D
      (powerRootCoefficientPDInput p f)) = algebraMap Nv Dv zv := by
    simpa only [principalDPGenerator_one] using perfectPrismPDTensorVarpiEquiv_generator W hW f 1
  rw [hInput, perfectPrismVarpiNativeDividedPowers_base_apply_of_unconditional]
  apply e.injective
  rw [e.apply_symm_apply]
  exact (perfectPrismPDTensorVarpiEquiv_generator W hW f i).symm

end Prism
end SerrePositivity.BhattScholze.Andre.VarpiComparison

end PDBaseChange

/-! ## BS 著者版 Remark 7.15（著者版 p.62）：具体的候補の係数表記の照合

## 概要
元の自然な Hodge–Tate 候補 T について、p 完全忠実平坦性と R/ϖ 上の
通常忠実平坦性を結び、同じ剰余の pd 底変換表示と fᵖ 商上の自由性を同時に公開する。

## 方針
自然な係数作用を保つ既存の代数同型により、pd 包の基底計算を実際の T/ϖ へ移す。

## 規約
既存の候補比較に現れる入力は f'=φ_A⁻¹(f) である。原典の φ_A 引戻しを省略して
元の f と同一視しない。prism 商の p 正則性とモニック性・正次数を明示する。

## 使われ方
E1.25・E1.55・E1.56 と原典の係数表記を照合する補足であり、主定理の引用には触れない。
-/

@[expose] public noncomputable section Candidate

namespace SerrePositivity.BhattScholze.Andre.VarpiComparison
open _root_.SerrePositivity.DerivedCompletion
open scoped _root_.TensorProduct
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "uL" => pdCompletionUnit L p (jL dP)
local notation "T" => H ⧸ Ideal.span {uL (jL dP)}
local notation "R" => A ⧸ W.ideal
local notation "v" => perfectPrismVarpi W hW
local notation "Rv" => R ⧸ Ideal.span {v}
local notation "φ" => powerRootPrismMonicHodgeTateBaseMap W hW f
local notation "Tv" => T ⧸ Ideal.map φ (Ideal.span {v})
local notation "Nv" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial Rv p hp
local notation "barr" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {v})) (Ideal.Quotient.mk W.ideal)
local notation "f'" => perfectPrismInverseFrobeniusPolynomial W hW f
local notation "zv" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap Rv p hp
  (Polynomial.map barr (perfectPrismInverseFrobeniusPolynomial W hW f))
local notation "Dv" => PrincipalDPPresentation Nv zv
local notation "Qv" => Nv ⧸ Ideal.span {zv ^ p}
local notation "hpv" => perfectPrismVarpiRootRing_prime_eq_zero W hW

/-- 概要：自然な候補の ϖ 商は同じ R/ϖ 上の pd 表示環と代数同型。
方針：既存の自然二重商比較と pd 剰余比較を合成する。
規約：入力は明示的な逆 Frobenius 係数変更 f'。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の自由性と忠実平坦性の同じ候補への移送。 -/
def hodgeTateVarpiPDAlgEquiv (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateAlgebra W hW f
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    Tv ≃ₐ[Rv] Dv := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateAlgebra W hW f
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := powerRootPrismMonicHodgeTatePDResidueAlgebra W hW f hf
  let e := powerRootPrismMonicHodgeTateVarpiMapQuotAlgEquiv W hW f hf
  let ePD := powerRootPrismMonicVarpiResidueAlgEquiv W hW f hf
  exact e.trans ePD

/-- 概要：候補の ϖ 商に入力の p 乗商の係数作用を与える。
方針：pd 表示環の標準作用を自然剰余との同型で戻す。
規約：R/ϖ 作用は既存の自然な作用を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の fᵖ 商上の自由性の型。 -/
@[instance_reducible] def hodgeTateVarpiPowerQuotientAlgebra (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateAlgebra W hW f
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    Algebra Qv Tv := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateAlgebra W hW f
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := principalDPQuotientAlgebra hp hpv zv
  exact ((hodgeTateVarpiPDAlgEquiv W hW f hf).symm.toRingHom.comp (algebraMap Qv Dv)).toAlgebra

set_option maxHeartbeats 2000000 in
-- 実完備化の二重商と移送した係数作用の同一性を展開するために必要。
/-- 概要：実際の T/ϖ は原典型の無限根入力の p 乗商上自由。
方針：切断分冪表示による既存の基底を係数作用と共に戻す。
規約：モニック性は候補比較に必要で、正次数と hpR はこの自由性には不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の自由性の文と同じ実対象の対応。 -/
theorem hodgeTateVarpi_free_over_powerQuotient (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateAlgebra W hW f
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := hodgeTateVarpiPowerQuotientAlgebra W hW f hf
    Module.Free Qv Tv := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateAlgebra W hW f
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := hodgeTateVarpiPowerQuotientAlgebra W hW f hf
  let := principalDPQuotientAlgebra hp hpv zv
  let e : Tv ≃ₐ[Qv] Dv :=
    { (hodgeTateVarpiPDAlgEquiv W hW f hf).toRingEquiv with
      commutes' := fun r => (hodgeTateVarpiPDAlgEquiv W hW f hf).apply_symm_apply _ }
  let := perfectPrismVarpiNativePDEnvelope_free_over_powerQuotient W hW f'
  exact Module.Free.of_equiv e.symm.toLinearEquiv

/-- 概要：候補の p 完全忠実平坦性は、自然な通常 ϖ 商の忠実平坦性と同値（BS 著者版 Remark 7.15 の証明中の被覆判定の比較）。
方針：基底・候補の ϖ 正則性を供給して一般の判定を使う。
規約：元の候補・基底射を固定し、hpR を明示する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の p 係数と ϖ 係数の照合。 -/
theorem hodgeTate_completelyFaithfullyFlat_iff
    (hpR : IsSMulRegular R (p : R)) (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateAlgebra W hW f
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T ↔ Module.FaithfullyFlat Rv Tv := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateAlgebra W hW f
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  constructor
  · intro hT
    exact algebraQuotient_faithfullyFlat v (p : R) p hp (perfectPrismVarpi_span_pow W hW) T hT
  · intro hTv
    have := hTv
    have hTensor := Module.FaithfullyFlat.of_linearEquiv Rv Tv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor T (Ideal.span {v})).symm.toLinearEquiv
    have hvR := regular_of_span_power_eq v (p : R) p hp (perfectPrismVarpi_span_pow W hW) hpR
    have hV := isCompletelyFaithfullyFlat_principal_of_regular v hvR T
      (powerRootPrismMonicHodgeTate_varpi_regular W hW hpR f hf) hTensor
    exact (completelyFaithfullyFlat_iff v (p : R) p hp (perfectPrismVarpi_span_pow W hW) T).mpr hV

/-- 概要：候補の p 完全忠実平坦性、自然 ϖ 剰余の忠実平坦性、f'ᵖ 商上の自由性、
実装の係数 pd 包の R/ϖ 底変換との同型を一つに集約する。
方針：pd 基底計算を自然商へ移し、正則性付き同値の逆方向で p 完全忠実平坦性を得る。
規約：f'=φ_A⁻¹(f) を保持し、原典の Frobenius 引戻しを省略しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）と E1.25・E1.55・E1.56 の公開照合定理。 -/
theorem hodgeTate_coefficient_comparison
    (hpR : IsSMulRegular R (p : R)) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateAlgebra W hW f
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := hodgeTateVarpiPowerQuotientAlgebra W hW f hf
    let := varpiCoefficientAlgebra W hW
    (IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T ↔ Module.FaithfullyFlat Rv Tv) ∧
      Module.Free Qv Tv ∧ Module.FaithfullyFlat Rv Tv ∧
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T ∧
      Nonempty (Rv ⊗[A ⧸ Ideal.span {(p : A)}] PowerRootCoefficientPDEnvelope p f' ≃+* Tv) := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateAlgebra W hW f
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := hodgeTateVarpiPowerQuotientAlgebra W hW f hf
  let := varpiCoefficientAlgebra W hW
  have hiff := hodgeTate_completelyFaithfullyFlat_iff W hW f hpR hf
  have hFF := powerRootPrismMonicHodgeTateVarpi_faithfullyFlat W hW f hf hdeg
  exact ⟨hiff, hodgeTateVarpi_free_over_powerQuotient W hW f hf, hFF, hiff.mpr hFF,
    ⟨(perfectPrismPDTensorVarpiEquiv W hW f').trans
      (hodgeTateVarpiPDAlgEquiv W hW f hf).symm.toRingEquiv⟩⟩

end SerrePositivity.BhattScholze.Andre.VarpiComparison

end Candidate

/-! ## BS 著者版 Remark 7.15（著者版 p.62）：正則性を追加しない係数テンソルの分冪構造

## 概要
R/ϖ への通常テンソル底変換に分冪構造と自然な分冪射を与える。

## 方針
射影的な正次数商から得た無条件の分冪降下を、既存の係数環同型で移送する。

## 規約
完全 prism とモニック入力を固定し、prism 商の p 正則性を仮定しない。
旧名は保持する。

## 使われ方
A1-c2 の係数比較を原典の実 pd 包として照合する。
-/

@[expose] public noncomputable section UnconditionalPD

namespace SerrePositivity.BhattScholze.Andre.VarpiComparison
open scoped _root_.TensorProduct
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 概要：分冪構造の環同型による移送は分冪射を与える。
方針：移送された分冪演算の計算公式を用いる。
規約：任意の環同型と分冪イデアルについて成立する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の二つの構造移送を合成する補助。 -/
private theorem unconditional_transport_isDPMorphism {B C : Type u} [CommRing B] [CommRing C]
    {I : Ideal B} {J : Ideal C} (e : B ≃+* C) (h : I.map e.toRingHom = J)
    (H : DividedPowers I) : H.IsDPMorphism (DividedPowers.ofRingEquiv h H) e.toRingHom := by
  refine ⟨h.le, ?_⟩
  intro n b hb
  exact DividedPowers.ofRingEquiv_dpow_apply h H

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "R₀" => A ⧸ Ideal.span {(p : A)}
local notation "x" => Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW)
local notation "Q" => R₀ ⧸ Ideal.span {x}
local notation "D" => PowerRootCoefficientPDEnvelope p f
local notation "Rv" => (A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}
local notation "Nv" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial Rv p hp
local notation "barr" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW})) (Ideal.Quotient.mk W.ideal)
local notation "zv" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap Rv p hp (f.map barr)
local notation "Dv" => PrincipalDPPresentation Nv zv

local notation "K" => Ideal.span {algebraMap R₀ D x}

/-- 概要：係数テンソルに追加正則性なしの分冪構造を与える。
方針：無条件の native 分冪構造を環同型で戻す。
規約：正次数イデアルは同型による像として固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 pd 底変換。 -/
def perfectPrismPDTensorVarpiDividedPowers_of_unconditional
    (hf : f.Monic) :
    let := varpiCoefficientAlgebra W hW
    DividedPowers ((principalDPPositiveIdeal zv).map
      (perfectPrismPDTensorVarpiEquiv W hW f).symm.toRingHom) := by
  let := varpiCoefficientAlgebra W hW
  exact DividedPowers.ofRingEquiv rfl
    (perfectPrismVarpiNativeDividedPowers_of_unconditional W hW f hf)

/-- 概要：底変換した実分冪構造で、入力の分冪は還元前の標準生成元の像になる。
方針：環同型の移送公式と全標準生成元の一致を使う。
規約：モニック性のみを使い、prism 商の p 正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の pd 包としての底変換の具体的計算。 -/
theorem perfectPrismPDTensorVarpiDividedPowers_generator_of_unconditional
    (hf : f.Monic) (i : ℕ) :
    let := varpiCoefficientAlgebra W hW
    (perfectPrismPDTensorVarpiDividedPowers_of_unconditional W hW f hf).dpow i
      (1 ⊗ₜ[R₀] algebraMap (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial R₀ p hp) D (powerRootCoefficientPDInput p f)) =
        1 ⊗ₜ[R₀] principalDPGenerator (powerRootCoefficientPDInput p f) i := by
  let := varpiCoefficientAlgebra W hW
  let e := perfectPrismPDTensorVarpiEquiv W hW f
  change e.symm ((perfectPrismVarpiNativeDividedPowers_of_unconditional W hW f hf).dpow i
    (e (1 ⊗ₜ[R₀] algebraMap (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial R₀ p hp) D
      (powerRootCoefficientPDInput p f)))) = _
  have hInput : e (1 ⊗ₜ[R₀] algebraMap (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial R₀ p hp) D
      (powerRootCoefficientPDInput p f)) = algebraMap Nv Dv zv := by
    simpa only [principalDPGenerator_one] using perfectPrismPDTensorVarpiEquiv_generator W hW f 1
  rw [hInput, perfectPrismVarpiNativeDividedPowers_base_apply_of_unconditional]
  apply e.injective
  rw [e.apply_symm_apply]
  exact (perfectPrismPDTensorVarpiEquiv_generator W hW f i).symm

/-- 概要：元の実 pd 包から係数テンソルへの標準射は分冪を保つ。
方針：無条件の係数還元の分冪射と二つの構造移送を合成する。
規約：全ての元で includeRight と照合し、hpR を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の pd 底変換の構造射。 -/
theorem perfectPrismPDTensorVarpi_isDPMorphism_of_unconditional
    (hf : f.Monic) :
    let := varpiCoefficientAlgebra W hW
    (powerRootCoefficientDividedPowers p W hW f hf).IsDPMorphism
      (perfectPrismPDTensorVarpiDividedPowers_of_unconditional W hW f hf)
      (Algebra.TensorProduct.includeRight : D →ₐ[R₀] Rv ⊗[R₀] D).toRingHom := by
  let := varpiCoefficientAlgebra W hW
  let e := perfectPrismPDTensorVarpiEquiv W hW f
  let e₀ := perfectPrismVarpiPDEnvelopeEquiv W hW f
  have hq := perfectPrismVarpiPowerRootDividedPowers_isDPMorphism_of_unconditional W hW f hf
  have h₀ := unconditional_transport_isDPMorphism e₀
    (perfectPrismVarpiPDEnvelopeEquiv_positiveIdeal W hW f)
    (perfectPrismVarpiPowerRootDividedPowers_of_unconditional W hW f hf)
  have ht := unconditional_transport_isDPMorphism e.symm rfl
    (perfectPrismVarpiNativeDividedPowers_of_unconditional W hW f hf)
  have hmid := DividedPowers.IsDPMorphism.comp
    (perfectPrismVarpiNativeDividedPowers_of_unconditional W hW f hf) h₀ hq
  have hc := DividedPowers.IsDPMorphism.comp
    (perfectPrismPDTensorVarpiDividedPowers_of_unconditional W hW f hf) ht hmid
  have he : (Algebra.TensorProduct.includeRight : D →ₐ[R₀] Rv ⊗[R₀] D).toRingHom =
      e.symm.toRingHom.comp (e₀.toRingHom.comp (Ideal.Quotient.mk K)) := by
    apply RingHom.ext
    intro t
    apply e.injective
    change e (1 ⊗ₜ[R₀] t) = e (e.symm (e₀ (Ideal.Quotient.mk K t)))
    rw [e.apply_symm_apply]
    exact perfectPrismPDTensorVarpiEquiv_one_tmul W hW f t
  rw [← he] at hc
  exact hc

end SerrePositivity.BhattScholze.Andre.VarpiComparison

end UnconditionalPD

/-! ## BS 著者版 Remark 7.15（著者版 p.62）：無条件の Hodge–Tate 係数比較

## 概要
元の候補 T の p 完全忠実平坦性と自然な ϖ 商の忠実平坦性を照合する。

## 方針
正次数では実際の導来 p 還元の次数零集中を用い、次数零では源 H の零環性を用いる。

## 規約
一般の通常商による判定には加群上の正則性が必要である。
この具体的候補では無条件の導来還元定理を使い、T 上の正則性を仮定しない。
f'=φ_A⁻¹(f) と既存の係数作用を保持する。旧名は削除しない。

## 使われ方
A1-c2 の公開比較を hpR なしで供給する。
-/

@[expose] public noncomputable section UnconditionalCandidate

namespace SerrePositivity.BhattScholze.Andre.VarpiComparison
open _root_.SerrePositivity.DerivedCompletion
open scoped _root_.TensorProduct
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "uL" => pdCompletionUnit L p (jL dP)
local notation "T" => H ⧸ Ideal.span {uL (jL dP)}
local notation "R" => A ⧸ W.ideal
local notation "v" => perfectPrismVarpi W hW
local notation "Rv" => R ⧸ Ideal.span {v}
local notation "φ" => powerRootPrismMonicHodgeTateBaseMap W hW f
local notation "Tv" => T ⧸ Ideal.map φ (Ideal.span {v})
local notation "Nv" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial Rv p hp
local notation "barr" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {v})) (Ideal.Quotient.mk W.ideal)
local notation "f'" => perfectPrismInverseFrobeniusPolynomial W hW f
local notation "zv" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap Rv p hp
  (Polynomial.map barr (perfectPrismInverseFrobeniusPolynomial W hW f))
local notation "Dv" => PrincipalDPPresentation Nv zv
local notation "Qv" => Nv ⧸ Ideal.span {zv ^ p}
local notation "hpv" => perfectPrismVarpiRootRing_prime_eq_zero W hW

/-- 概要：元の候補の p 完全忠実平坦性は自然な ϖ 商の忠実平坦性と同値。
方針：正次数では無条件の導来還元を使い、次数零では源の零環性から平坦性を得る。
規約：モニック性のみを仮定し、hpR と余分な正次数仮定を置かない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の二つの係数表記の照合。 -/
theorem hodgeTate_completelyFaithfullyFlat_iff_of_unconditional (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateAlgebra W hW f
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T ↔ Module.FaithfullyFlat Rv Tv := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateAlgebra W hW f
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  constructor
  · intro hT
    exact algebraQuotient_faithfullyFlat v (p : R) p hp (perfectPrismVarpi_span_pow W hW) T hT
  · intro hTv
    by_cases hz : f.natDegree = 0
    · let : Subsingleton H :=
        powerRootPrismMonic_pdCompletion_subsingleton_of_natDegree_zero W hW f hf hz
      have hCF : IsCompletelyFlat (Ideal.span {v}) T := by
        intro N _ _ _
        apply (isConcentratedInDegreeZero_derivedTensor_iff T N).mpr
        intro i hi
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
        exact torModule_subsingleton_of_flat T N j
      have := hTv
      have hTensor := Module.FaithfullyFlat.of_linearEquiv Rv Tv
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor T (Ideal.span {v})).symm.toLinearEquiv
      exact (completelyFaithfullyFlat_iff v (p : R) p hp
        (perfectPrismVarpi_span_pow W hW) T).mpr ⟨hCF, hTensor⟩
    · exact powerRootPrismMonicHodgeTate_prime_completelyFaithfullyFlat_of_unconditional
        W hW f hf (Nat.pos_of_ne_zero hz)

/-- 概要：候補の p 完全忠実平坦性、自然 ϖ 剰余の忠実平坦性、f'ᵖ 商上の自由性、
実装の係数 pd 包の R/ϖ 底変換との同型を一つに集約する。
方針：pd 基底計算を自然商へ移し、無条件版の同値で p 完全忠実平坦性を得る。
規約：f'=φ_A⁻¹(f) を保持し、原典の Frobenius 引戻しを省略しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）と E1.25・E1.55・E1.56 の公開照合定理。 -/
theorem hodgeTate_coefficient_comparison_of_unconditional
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateAlgebra W hW f
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := hodgeTateVarpiPowerQuotientAlgebra W hW f hf
    let := varpiCoefficientAlgebra W hW
    (IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T ↔ Module.FaithfullyFlat Rv Tv) ∧
      Module.Free Qv Tv ∧ Module.FaithfullyFlat Rv Tv ∧
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T ∧
      Nonempty (Rv ⊗[A ⧸ Ideal.span {(p : A)}] PowerRootCoefficientPDEnvelope p f' ≃+* Tv) := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateAlgebra W hW f
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := hodgeTateVarpiPowerQuotientAlgebra W hW f hf
  let := varpiCoefficientAlgebra W hW
  have hiff := hodgeTate_completelyFaithfullyFlat_iff_of_unconditional W hW f hf
  have hFF := powerRootPrismMonicHodgeTateVarpi_faithfullyFlat W hW f hf hdeg
  exact ⟨hiff, hodgeTateVarpi_free_over_powerQuotient W hW f hf, hFF, hiff.mpr hFF,
    ⟨(perfectPrismPDTensorVarpiEquiv W hW f').trans
      (hodgeTateVarpiPDAlgEquiv W hW f hf).symm.toRingEquiv⟩⟩

end SerrePositivity.BhattScholze.Andre.VarpiComparison

end UnconditionalCandidate

/-! ## BS 著者版 Remark 7.15（著者版 p.62）の自然な係数テンソル射は分冪射
旧ファイルは `Andre/Remark715/VarpiComparison/PDCompatibility.lean`。

## 概要
実装の A/p 上の実 pd 包から R/ϖ への通常テンソル底変換は分冪演算を保つ。

## 方針
射影的係数商への分冪射と二つの構造移送を合成し、全ての元で自然な射と照合する。
原典の p ねじれなしへの帰着とは異なる証明経路。

## 規約
モニック入力のみを仮定する。標準生成元だけの照合で代用しない。

## 使われ方
原典側の pd 包の普遍性と通常のテンソル底変換の対応を保証する。
-/

@[expose] public noncomputable section PDCompatibility

namespace SerrePositivity.BhattScholze.Andre.VarpiComparison
open scoped _root_.TensorProduct
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 分冪構造の環同型による移送は分冪射を与える。BS 著者版 Remark 7.15（著者版 p.62）への補助。 -/
private theorem transport_isDPMorphism {B C : Type u} [CommRing B] [CommRing C]
    {I : Ideal B} {J : Ideal C} (e : B ≃+* C) (h : I.map e.toRingHom = J)
    (H : DividedPowers I) : H.IsDPMorphism (DividedPowers.ofRingEquiv h H) e.toRingHom := by
  refine ⟨h.le, ?_⟩
  intro n b hb
  exact DividedPowers.ofRingEquiv_dpow_apply h H

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "R₀" => A ⧸ Ideal.span {(p : A)}
local notation "x" => Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW)
local notation "D" => PowerRootCoefficientPDEnvelope p f
local notation "K" => Ideal.span {algebraMap R₀ D x}
local notation "Rv" => (A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}

/-- 概要：元の実 pd 包から係数テンソル底変換への標準射は分冪を保つ（BS 著者版 Remark 7.15 の証明中の φ 引き戻しの PD 比較の一方向）。
方針：射影的係数商の分冪射を構造移送と合成し、全元で includeRight と同一視する。
規約：元の環と係数作用を保持し、hpR と正次数を要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の pd 包の底変換を実分冪射として供給する。 -/
theorem perfectPrismPDTensorVarpi_isDPMorphism
    (hf : f.Monic) :
    let := varpiCoefficientAlgebra W hW
    (powerRootCoefficientDividedPowers p W hW f hf).IsDPMorphism
      (perfectPrismPDTensorVarpiDividedPowers W hW f hf)
      (Algebra.TensorProduct.includeRight : D →ₐ[R₀] Rv ⊗[R₀] D).toRingHom := by
  let := varpiCoefficientAlgebra W hW
  let e := perfectPrismPDTensorVarpiEquiv W hW f
  let e₀ := perfectPrismVarpiPDEnvelopeEquiv W hW f
  have hq := perfectPrismVarpiPowerRootDividedPowers_isDPMorphism_of_unconditional W hW f hf
  have h₀ := transport_isDPMorphism e₀
    (perfectPrismVarpiPDEnvelopeEquiv_positiveIdeal W hW f)
    (perfectPrismVarpiPowerRootDividedPowers_of_unconditional W hW f hf)
  have ht := transport_isDPMorphism e.symm rfl
    (perfectPrismVarpiNativeDividedPowers_of_unconditional W hW f hf)
  have hmid := DividedPowers.IsDPMorphism.comp
    (perfectPrismVarpiNativeDividedPowers_of_unconditional W hW f hf) h₀ hq
  have hc := DividedPowers.IsDPMorphism.comp
    (perfectPrismPDTensorVarpiDividedPowers W hW f hf) ht hmid
  have he : (Algebra.TensorProduct.includeRight : D →ₐ[R₀] Rv ⊗[R₀] D).toRingHom =
      e.symm.toRingHom.comp (e₀.toRingHom.comp (Ideal.Quotient.mk K)) := by
    apply RingHom.ext
    intro t
    apply e.injective
    change e (1 ⊗ₜ[R₀] t) = e (e.symm (e₀ (Ideal.Quotient.mk K t)))
    rw [e.apply_symm_apply]
    exact perfectPrismPDTensorVarpiEquiv_one_tmul W hW f t
  rw [← he] at hc
  exact hc

end SerrePositivity.BhattScholze.Andre.VarpiComparison

end PDCompatibility

/-! ## BS 著者版 Remark 7.15（著者版 p.62）：R/p から R/ϖ への pd 底変換

## 概要
実装の A/p 表示との比較とは別に、R/p 上の無限根 pd 表示を R/ϖ へ底変換する。

## 方針
一般の係数商と係数環同型を組み合わせ、(R/p)/(ϖ)≃R/ϖ を使う。

## 規約
通常表示環の同型なのでモニック性・正則性は不要。実分冪射は PDCompatibility に置く。

## 使われ方
原典の R/ϖ⊗_{R/p} という係数表記を実際のテンソル積型として供給する。
-/

@[expose] public noncomputable section PrimeReduction

namespace SerrePositivity.BhattScholze.Andre.VarpiComparison
open scoped _root_.TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 概要：係数環同型は無限根環での多項式評価と可換。
方針：係数単項式と標準変数の像を照合する。
規約：指数モノイドは変更しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の二重商係数の移送。 -/
theorem rootCoefficientChange_baseMap {S B : Type u} [CommRing S] [CommRing B]
    (p : ℕ) (hp : 0 < p) (e : S ≃+* B) (f : Polynomial S) :
    AddMonoidAlgebra.mapRingEquiv (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentMonoid p hp) e
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap S p hp f) =
        _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap B p hp (f.map e.toRingHom) := by
  simp only [_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap, Polynomial.aeval_def, Polynomial.eval₂_map]
  change (AddMonoidAlgebra.mapRingEquiv (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentMonoid p hp) e).toRingHom
    (Polynomial.eval₂ (algebraMap S (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial S p hp))
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable S p hp 0) f) = _
  rw [Polynomial.hom_eval₂]
  have hv : AddMonoidAlgebra.mapRingEquiv (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentMonoid p hp) e
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable S p hp 0) = _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable B p hp 0 := by
    simp only [_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable, AddMonoidAlgebra.mapRingEquiv_single, map_one]
  change Polynomial.eval₂ _
    (AddMonoidAlgebra.mapRingEquiv (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentMonoid p hp) e
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable S p hp 0)) f = _
  rw [hv]
  congr 1
  apply RingHom.ext
  intro s
  change AddMonoidAlgebra.mapRingEquiv (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentMonoid p hp) e
    (algebraMap S (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial S p hp) s) =
      algebraMap B (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial B p hp) (e s)
  simp [AddMonoidAlgebra.coe_algebraMap, AddMonoidAlgebra.mapRingEquiv_single]

section Change
variable (S B : Type u) [CommRing S] [CommRing B] (c : S)
variable (e : (S ⧸ Ideal.span {c}) ≃+* B)

/-- 概要：指定係数商同型による自然な係数代数構造。
方針：標準商射と同型を合成する。規約：作用を明示的に固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の原典係数でのテンソル型。 -/
@[instance_reducible] def quotientCoefficientAlgebra : Algebra S B :=
  (e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {c}))).toAlgebra

/-- 概要：係数商同型を指定作用上の代数同型として扱う。
方針：係数作用の定義を展開する。規約：同型は元の環同型と同じ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）のテンソル因子の変更。 -/
def quotientCoefficientAlgEquiv :
    let := quotientCoefficientAlgebra S B c e
    (S ⧸ Ideal.span {c}) ≃ₐ[S] B := by
  let := quotientCoefficientAlgebra S B c e
  exact { e with commutes' := fun _ => rfl }

/-- 概要：係数商と係数同型の合成に沿う無限根 pd 表示の実テンソル同型。
方針：一般の係数商底変換と、入力評価を保つ係数環同型を合成する。
規約：入力多項式は元の S から指定した係数射で移す。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の R/p と R/ϖ の直接比較。 -/
def powerRootPDTensorChangeEquiv (p : ℕ) (hp : 0 < p) (f : Polynomial S) :
    let := quotientCoefficientAlgebra S B c e
    B ⊗[S] PrincipalDPPresentation (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial S p hp)
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap S p hp f) ≃+*
        PrincipalDPPresentation (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial B p hp)
          (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap B p hp
            (f.map (e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {c}))))) := by
  let := quotientCoefficientAlgebra S B c e
  let D := PrincipalDPPresentation (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial S p hp)
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap S p hp f)
  refine ((Algebra.TensorProduct.congr (quotientCoefficientAlgEquiv S B c e).symm
    (AlgEquiv.refl : D ≃ₐ[S] D)).toRingEquiv.trans
      (powerRootPDTensorQuotientEquiv S p hp c f)).trans ?_
  refine principalDPRingEquivOfEq
    (AddMonoidAlgebra.mapRingEquiv (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentMonoid p hp) e) _ _ ?_
  rw [rootCoefficientChange_baseMap, Polynomial.map_map]
end Change

/-- 概要：R/p の pd 表示を原典の R/ϖ へテンソルすると、同じ f の R/ϖ pd 表示となる。
方針：(ϖ^p)=(p) による二重商同型を一般の係数テンソル比較へ渡す。
規約：R は任意の可換環でよく、入力 f のモニック性は環同型には不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の R/ϖ⊗_{R/p} による係数表記の照合。 -/
def primePDTensorVarpiEquiv {R : Type u} [CommRing R] (p : ℕ) (hp : 0 < p)
    (v : R) (hspan : Ideal.span {v ^ p} = Ideal.span {(p : R)}) (f : Polynomial R) :
    let e := primeVarpiDoubleQuotientEquiv v (p : R) p hp hspan
    let := quotientCoefficientAlgebra (R ⧸ Ideal.span {(p : R)}) (R ⧸ Ideal.span {v})
      (Ideal.Quotient.mk (Ideal.span {(p : R)}) v) e
    (R ⧸ Ideal.span {v}) ⊗[R ⧸ Ideal.span {(p : R)}]
      PrincipalDPPresentation (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial (R ⧸ Ideal.span {(p : R)}) p hp)
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap (R ⧸ Ideal.span {(p : R)}) p hp
          (f.map (Ideal.Quotient.mk (Ideal.span {(p : R)})))) ≃+*
      PrincipalDPPresentation (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial (R ⧸ Ideal.span {v}) p hp)
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap (R ⧸ Ideal.span {v}) p hp
          (f.map (Ideal.Quotient.mk (Ideal.span {v})))) := by
  let e := primeVarpiDoubleQuotientEquiv v (p : R) p hp hspan
  let := quotientCoefficientAlgebra (R ⧸ Ideal.span {(p : R)}) (R ⧸ Ideal.span {v})
    (Ideal.Quotient.mk (Ideal.span {(p : R)}) v) e
  have hcoeff : (e.toRingHom.comp (Ideal.Quotient.mk _)).comp
      (Ideal.Quotient.mk (Ideal.span {(p : R)})) = Ideal.Quotient.mk (Ideal.span {v}) := by
    ext r
    rfl
  have h := powerRootPDTensorChangeEquiv (R ⧸ Ideal.span {(p : R)}) (R ⧸ Ideal.span {v})
    (Ideal.Quotient.mk (Ideal.span {(p : R)}) v) e p hp
    (f.map (Ideal.Quotient.mk (Ideal.span {(p : R)})))
  rw [Polynomial.map_map, hcoeff] at h
  exact h

end SerrePositivity.BhattScholze.Andre.VarpiComparison

end PrimeReduction

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Rem 7.15" (partial := special) "主張（R→S が mod p で ind-syntomic な被覆）は証明していない。使っているのは構成の部分：S=R⟨Y^{1/p^∞}⟩/(f(Y)) の prismatic envelope T と φ^*(T/ϖ) の pd 包の記述、cover 性（完全忠実平坦）で、これが Thm 7.14 の一段拡大になる。docstring の「BS Rem 7.15」引用（1,700 件超）はこの計算を指す ／ DOC1 照合（11-07、Codex が型で確認）：項目そのものではないので宣言の列から外したもの：exists_monicRootPerfectoidExtension（Andre/Transfinite/Tower.lean:1172。型は R からの一段拡大の存在。原文が直接扱う方程式商 S から T への被覆や mod p ind-syntomic ） ／ DOC1 照合：ok 3 件"] _root_.SerrePositivity.BhattScholze.Andre.VarpiComparison.hodgeTate_completelyFaithfullyFlat_iff
attribute [cite BS19 "Rem 7.15" (partial := special) "主張（R→S が mod p で ind-syntomic な被覆）は証明していない。使っているのは構成の部分：S=R⟨Y^{1/p^∞}⟩/(f(Y)) の prismatic envelope T と φ^*(T/ϖ) の pd 包の記述、cover 性（完全忠実平坦）で、これが Thm 7.14 の一段拡大になる。docstring の「BS Rem 7.15」引用（1,700 件超）はこの計算を指す ／ DOC1 照合（11-07、Codex が型で確認）：項目そのものではないので宣言の列から外したもの：exists_monicRootPerfectoidExtension（Andre/Transfinite/Tower.lean:1172。型は R からの一段拡大の存在。原文が直接扱う方程式商 S から T への被覆や mod p ind-syntomic ） ／ DOC1 照合：ok 3 件"] _root_.SerrePositivity.BhattScholze.Andre.VarpiComparison.perfectPrismPDTensorVarpi_isDPMorphism
