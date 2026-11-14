module

public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.CompletionPrism
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Unconditional.FrobeniusPD
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Completion
public import SerrePositivity.HomologicalAlgebra.TorAlgebraAcyclicBaseChange
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete
public import SerrePositivity.BhattScholze.Andre.Variants.RootedExtension
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Unconditional.Source
public import SerrePositivity.BhattScholze.Andre.Perfection.DeltaAlgebra
public import SerrePositivity.BhattScholze.Andre.Variants.Auxiliary

/-!
# 完全化と完全忠実平坦性（原典の「cover」の部分）

## 概要
Hodge–Tate 商の完備性と完全忠実平坦性、完備化の二元完全平坦性と剰余 H⁰ の忠実平坦性、完全 δ 化後の剰余、無限根候補の完全 δ 化と perfectoid 商・その p 完全忠実平坦性。
BS 著者版 Remark 7.15 の被覆性に関わる、完全化と完全忠実平坦性の比較を与える。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`PowerRootEnvelope/VarpiComparison`、`Variants/MonicRootedExtension`。
-/

universe u

/-! ## André Hodge–Tate 商の完全忠実平坦性の移行

## 概要

元の正次数モニック源の Hodge–Tate 商の完全忠実平坦性は、hpR を要求しない証明を使う。
BS 著者版 Remark 7.15（著者版 p.62）の元の候補を変更しない。

## 方針

旧 hpR 付き公開定理の全呼出しを
`powerRootPrismMonicHodgeTate_prime_completelyFaithfullyFlat_of_unconditional` へ移す。
原典の p ねじれなしへの帰着とは異なる実源の純性による経路。

## 規約

旧定理は不要になったため削除した。正次数仮定は忠実性のため保持する。

## 使われ方

既存の import 経路で無条件版を公開し、元の H の二元完全平坦性へ渡す。
-/

/-! ## 元の無限根モニック実完備化の二元完全平坦性

## 概要

元の実完備化 H は、元の完全 prism の係数作用について (p,d) 完全平坦。
BS 著者版 Remark 7.15（著者版 p.62）の δ 完全化に渡す導来剰余の計算。

## 方針

自然な H/d の係数作用と標準主環商の作用を照合し、d の正則性から p 完全平坦性を戻す。

基礎となる Hodge–Tate 商の完全忠実平坦性は、原典と異なる実源の純性による無条件版を使う。

## 規約

元の実 H⁰ と標準係数射を保持する。モニック性・正次数を明示し、prism 商の p 正則性は要求しない。

## 使われ方

元の H の導来 (p,d) 剰余を δ 完全化の一般剰余判定へ渡す。
-/

@[expose] public noncomputable section PowerRootPrismMonicCompletionPairFlat

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


/-- 概要：元の係数環 A に関する実完備化の自然な代数構造。
方針：検証済みの標準係数射から構成する。
規約：モニック性と p 正則性は作用の定義自体に不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A 作用での導来剰余。 -/
@[instance_reducible] def powerRootPrismMonicCompletionAlgebra :
    let := pdCompletionCommRing L p (jL dP)
    Algebra A H := by
  let := pdCompletionCommRing L p (jL dP)
  exact (powerRootPrismMonicCompletionBaseMap W hW f).toAlgebra

/-- 概要：H/d の自然な基底商作用は標準主環商の作用と一致する。
方針：商基底の元を A の代表元へ戻して標準係数射を照合する。
規約：同じ実完備化の同じ分母商を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の正則主剰余判定の係数作用。 -/
theorem powerRootPrismMonicHodgeTateAlgebra_eq_principal :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicCompletionAlgebra W hW f
    powerRootPrismMonicHodgeTateAlgebra W hW f =
      principalAdicQuotientAlgebra W.generator H := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicCompletionAlgebra W hW f
  apply Algebra.algebra_ext
  intro r
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  rfl

include hf hdeg in
/-- 概要：元の無限根モニック実完備化は (p,d) 完全平坦。
方針：分母正則性と標準作用に移した H/d の p 完全平坦性を一般判定へ渡す。
規約：元の A 係数作用と実 H⁰ を用いる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完全 δ 化の導来剰余入力。 -/
theorem powerRootPrismMonicCompletion_pair_completelyFlat :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicCompletionAlgebra W hW f
    IsCompletelyFlat (Ideal.span {(p : A), W.generator}) H := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicCompletionAlgebra W hW f
  have hreg : IsSMulRegular H (algebraMap A H W.generator) :=
    powerRootPrismMonicRaw_pdCompletion_generator_regular W hW f hf
  have hred : let := principalAdicQuotientAlgebra W.generator H
      IsCompletelyFlat (Ideal.span {(p : A ⧸ Ideal.span {W.generator})})
        (H ⧸ Ideal.span {algebraMap A H W.generator}) := by
    rw [← powerRootPrismMonicHodgeTateAlgebra_eq_principal W hW f]
    exact (powerRootPrismMonicHodgeTate_prime_completelyFaithfullyFlat_of_unconditional
      W hW f hf hdeg).1
  apply completelyFlat_pair_algebra_of_regular_reduction (p : A) W.generator
    W.generator_regular H hreg
  simpa only [map_natCast] using hred

/-- 概要：標準係数射で制限した加群は元の自然な A 代数と線形同型。
方針：制限スカラー加群と代数作用の標準比較を使う。
規約：元の実完備化の係数射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の導来底変換への入力。 -/
def powerRootPrismMonicCompletionScalarEquiv :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicCompletionAlgebra W hW f
    baseChangeScalarModule (powerRootPrismMonicCompletionBaseMap W hW f) ≃ₗ[A] H := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicCompletionAlgebra W hW f
  exact baseChangeScalarAlgebraEquiv (B := H)

include hf hdeg in
/-- 概要：元の実完備化の (p,d) 標準底変換の高次 Tor は零。
方針：二元完全平坦性を標準剰余係数加群へ適用する。
規約：標準係数作用を持つ加群そのものを使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の導来剰余の離散性。 -/
theorem powerRootPrismMonicCompletion_pair_scalarExtensionTorVanishing :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicCompletionAlgebra W hW f
    scalarExtensionTorVanishing (Ideal.Quotient.mk (Ideal.span {(p : A), W.generator}))
      (baseChangeScalarModule (powerRootPrismMonicCompletionBaseMap W hW f)) := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicCompletionAlgebra W hW f
  apply scalarExtensionTorVanishing_of_completelyFlat
  exact isCompletelyFlat_of_linearEquiv _
    (powerRootPrismMonicCompletionScalarEquiv W hW f).symm
    (powerRootPrismMonicCompletion_pair_completelyFlat W hW f hf hdeg)

include hf hdeg in
/-- 概要：元の実完備化の導来 (p,d) 剰余は非零次数で消える。
方針：高次 Tor の消滅から標準増大同型を作り、単項複体のホモロジーを使う。
規約：標準係数射で制限した実加群の導来底変換を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の δ 完全化の剰余計算。 -/
theorem powerRootPrismMonicCompletion_pair_reduction_homology_isZero
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
    (powerRootPrismMonicCompletion_pair_scalarExtensionTorVanishing W hW f hf hdeg)
  exact (derivedSingleHomology_isZero ((ModuleCat.extendScalars q).obj M) i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat _) i).mapIso
      (DerivedCategory.Minus.ι.mapIso e))

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicCompletionPairFlat

/-! ## 元の実完備化の二元剰余 H⁰ の忠実平坦性

## 概要

元の実完備化 H の標準 (p,d) 剰余と導来剰余 H⁰ は忠実平坦。
BS 著者版 Remark 7.15（著者版 p.62）の δ 完全化への入力をそろえる。

## 方針

同じ自然な H/d の p 完全忠実平坦性を二段スカラー拡大と H⁰ 比較で移す。

基礎となる Hodge–Tate 商の完全忠実平坦性は、原典と異なる実源の純性による無条件版を使う。

## 規約

元の係数射を保持し、モニック性・正次数を明示し、prism 商の p 正則性は要求しない。

## 使われ方

完全 δ 基底での Frobenius 段と余極限の剰余忠実平坦性へ渡す。
-/

@[expose] public noncomputable section PowerRootPrismMonicCompletionPairFaithful

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
/-- 概要：元の実完備化の標準二元剰余は忠実平坦。
方針：自然な主環商作用を照合し、二段剰余の一般判定を適用する。
規約：元の標準係数射で制限した実加群を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の導来二元剰余 H⁰。 -/
theorem powerRootPrismMonicCompletion_pair_scalarExtension_faithfullyFlat :
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
    exact powerRootPrismMonicHodgeTate_prime_completelyFaithfullyFlat_of_unconditional
      W hW f hf hdeg
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
theorem powerRootPrismMonicCompletion_pair_reductionH0_faithfullyFlat :
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
  let := powerRootPrismMonicCompletion_pair_scalarExtension_faithfullyFlat W hW f hf hdeg
  exact Module.FaithfullyFlat.of_linearEquiv _ ((ModuleCat.extendScalars q).obj M)
    ((boundedAboveDerivedBaseChangeModuleH0Iso q).app M).toLinearEquiv

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicCompletionPairFaithful

/-! ## 元の無限根モニック実候補の完全 δ 化と perfectoid 商

## 概要

元の raw 包の実完備化を δ 完全化し再完備化した生成元商は整 perfectoid。
元の Hodge–Tate 候補から自然に写り、元の多項式の根を標準射で送る。
BS 著者版 Corollary 7.3（著者版 p.56）、BS 著者版 Remark 7.15（p.62）の構成比較。

## 方針

任意 raw 包の一般比較を無限根モニック入力に適用する。
標準分母像を殺す自然射を商へ降ろし、多項式評価の自然性で根を移す。

## 規約

この完全化を経る基底射の p 完全忠実平坦性の保存は別工程。
perfectoid 性と根だけで一般存在目標の完成とは数えない。

## 使われ方

元の実候補の平坦性を最終 perfectoid 候補へ移す際の、同じ対象と標準射の固定。
-/

@[expose] public noncomputable section PowerRootPrismMonicCompletedPerfection

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.SerrePositivity.DerivedCompletion
/-- 概要：係数射で評価して零となる根は、任意の環射で送っても根。
方針：多項式評価と環射の可換性を使う。
規約：可換環を任意に扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の標準比較による根の移送。 -/
theorem polynomialRoot_mapRingHom {R S U : Type u} [CommRing R] [CommRing S] [CommRing U]
    (f : Polynomial R) (φ : R →+* S) (g : S →+* U) (r : S) (hr : f.eval₂ φ r = 0) :
    f.eval₂ (g.comp φ) (g r) = 0 := by
  rw [← Polynomial.hom_eval₂, hr, map_zero]

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "xP" => algebraMap A P (perfectPrismVarpiLift W hW)
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "uL" => pdCompletionUnit L p (jL dP)
local notation "dH" => uL (jL dP)
local notation "xH" => uL (jL xP)
local notation "T" => H ⧸ Ideal.span {dH}
local notation "qH" => Ideal.Quotient.mk (Ideal.span {dH})
local notation "R" => A ⧸ W.ideal
local notation "S" => H ⧸ Ideal.span {dH, xH}



local notation "DH" => deltaPDCompletionStructure (deltaAdjoinDivisionStructure E dP a) (jL dP)
local notation "C" => DeltaPerfection DH
local notation "x" => deltaPerfectionOf DH 0 dH
local notation "H∞" => PDCompletionH0 C p x
local notation "sC" => pdCompletionUnit C p x
local notation "T∞" => H∞ ⧸ Ideal.span {sC x}
local notation "q∞" => Ideal.Quotient.mk (Ideal.span {sC x})
local notation "hdP" => powerRootPrismGenerator_isDistinguished W hW

/-- 概要：元の実候補の完全 δ 化後の商は既存の perfectoid 候補と環同型。
方針：任意 raw 包の実完備化先行比較を同じ入力へ適用する。
規約：モニック性・正次数・prism 商の p 正則性は不要。
使われ方：BS 著者版 Corollary 7.3（著者版 p.56）、BS 著者版 Remark 7.15（p.62）の最終候補の固定。 -/
def powerRootPrismMonicCompletedPerfectionQuotientEquiv :
    let := pdCompletionCommRing L p (jL dP)
    let := pdCompletionCommRing C p x
    let := divisionPrismCommRing E dP a
    T∞ ≃+* DivisionPerfectoidCandidate E dP a hdP := by
  let := pdCompletionCommRing L p (jL dP)
  let := pdCompletionCommRing C p x
  let := divisionPrismCommRing E dP a
  exact rawDivisionPDPerfectionQuotientEquiv E dP a hdP

/-- 概要：完全 δ 化後の同じ標準生成元商は整 perfectoid。
方針：一般の raw 比較から整 perfectoid 性を受け取る。
規約：平坦性をこの主張に含めない。
使われ方：BS 著者版 Corollary 7.3（著者版 p.56）、BS 著者版 Remark 7.15（p.62）の根付き候補の環性質。 -/
theorem powerRootPrismMonicCompletedPerfection_isIntegralPerfectoid :
    let := pdCompletionCommRing L p (jL dP)
    let := pdCompletionCommRing C p x
    IsIntegralPerfectoid T∞ p := by
  let := pdCompletionCommRing L p (jL dP)
  let := pdCompletionCommRing C p x
  exact rawDivisionPDPerfectionQuotient_isIntegralPerfectoid E dP a hdP

set_option maxHeartbeats 2000000 in
-- 元の実 H⁰ とその完全化後の実 H⁰ の二つの巨大な環構造の照合に必要。
/-- 概要：元の Hodge–Tate 候補から完全 δ 化後の perfectoid 商への自然射。
方針：実 H⁰ の完全化標準射が元の分母像を殺すことから商へ降ろす。
規約：元の raw 包・実 H⁰ と標準射を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根と基底作用の追跡。 -/
def powerRootPrismMonicHodgeTateToCompletedPerfection :
    let := pdCompletionCommRing L p (jL dP)
    let := pdCompletionCommRing C p x
    T →+* T∞ := by
  let := pdCompletionCommRing L p (jL dP)
  let G := DH
  let Cp := DeltaPerfection G
  let i := deltaPerfectionOf G 0
  let xp := i dH
  let := pdCompletionCommRing Cp p xp
  let unitC := pdCompletionUnit Cp p xp
  let qC := Ideal.Quotient.mk (Ideal.span {unitC xp})
  let k := qC.comp (unitC.comp i)
  apply Ideal.Quotient.lift (Ideal.span {dH}) k
  change Ideal.span {dH} ≤ RingHom.ker k
  apply Ideal.span_le.mpr
  intro z hz
  rcases Set.mem_singleton_iff.mp hz with rfl
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (unitC xp))

set_option maxHeartbeats 800000 in
-- B4（Pair を Principal の反復に、11-04）：反復した PD 完備化の環構造の比較が深くなるので、この定義に限って上限を増やす。
/-- 概要：完全 δ 化後の商への基底射は元の自然基底射の合成。
方針：二つの標準射を合成する。
規約：基底は元の prism 商 R。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の平坦性を定式化する係数射。 -/
def powerRootPrismMonicCompletedPerfectionBaseMap :
    let := pdCompletionCommRing L p (jL dP)
    let := pdCompletionCommRing C p x
    R →+* T∞ := by
  let := pdCompletionCommRing L p (jL dP)
  let := pdCompletionCommRing C p x
  exact (powerRootPrismMonicHodgeTateToCompletedPerfection W hW f).comp
    (powerRootPrismMonicHodgeTateBaseMap W hW f)

set_option maxHeartbeats 800000 in
-- B4（Pair を Principal の反復に、11-04）：反復した PD 完備化の環構造の比較が深くなるので、この定義に限って上限を増やす。
/-- 概要：完全 δ 化後の根は元の実候補の指定根の標準像。
方針：検証済みの根を自然比較射で送る。
規約：別の根を選択し直さない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の同じ候補の根方程式。 -/
def powerRootPrismMonicCompletedPerfectionRoot :
    let := pdCompletionCommRing L p (jL dP)
    let := pdCompletionCommRing C p x
    T∞ := by
  let := pdCompletionCommRing L p (jL dP)
  let := pdCompletionCommRing C p x
  exact powerRootPrismMonicHodgeTateToCompletedPerfection W hW f
    (powerRootPrismMonicHodgeTateRoot W hW f)

/-- 概要：完全 δ 化後の指定根も元の多項式の係数商の根。
方針：評価と環射の可換性で元の実候補の根方程式を送る。
規約：モニック性・正次数・prism 商の p 正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根付き perfectoid 候補。 -/
theorem powerRootPrismMonicCompletedPerfectionRoot_eval :
    let := pdCompletionCommRing L p (jL dP)
    let := pdCompletionCommRing C p x
    (f.map (Ideal.Quotient.mk W.ideal)).eval₂
      (powerRootPrismMonicCompletedPerfectionBaseMap W hW f)
      (powerRootPrismMonicCompletedPerfectionRoot W hW f) = 0 := by
  let := pdCompletionCommRing L p (jL dP)
  let := pdCompletionCommRing C p x
  exact polynomialRoot_mapRingHom (f.map (Ideal.Quotient.mk W.ideal))
    (powerRootPrismMonicHodgeTateBaseMap W hW f)
    (powerRootPrismMonicHodgeTateToCompletedPerfection W hW f)
    (powerRootPrismMonicHodgeTateRoot W hW f) (powerRootPrismMonicHodgeTateRoot_eval W hW f)

/-- 概要：完全化後の商比較は全ての無限根入力係数の標準像を保つ。
方針：一般 raw 比較の係数射公式を入力環の元で評価する。
規約：全ての入力環元 r を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の既存候補との基底作用の一致。 -/
theorem powerRootPrismMonicCompletedPerfectionQuotientEquiv_coeff (r : P) :
    let := pdCompletionCommRing L p (jL dP)
    let := pdCompletionCommRing C p x
    let := divisionPrismCommRing E dP a
    powerRootPrismMonicCompletedPerfectionQuotientEquiv W hW f
      (q∞ (sC (deltaPerfectionOf DH 0 (uL (jL r))))) =
      divisionPerfectoidCandidateMap E dP a hdP r := by
  let := pdCompletionCommRing L p (jL dP)
  let := pdCompletionCommRing C p x
  let := divisionPrismCommRing E dP a
  exact RingHom.congr_fun (rawDivisionPDPerfectionQuotientEquiv_comp_coefficient E dP a hdP) r

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicCompletedPerfection

/-! ## 任意のモニック入力の Hodge–Tate 商の完備性

## 概要

元の実完備化 H の標準分母商は、次数零を含む全モニック入力について p 完備。
BS 著者版 Remark 7.15（著者版 p.62）の prismatic 源の商の完備性を述べる。

## 方針

正次数では同じ商の有界 p ねじれと導来完備性、次数零では同じ H の零環性を使う。
原典の p ねじれなしへの帰着とは異なる純性と有界ねじれによる証明経路。

## 規約

prism 商の p 正則性も入力の正次数も追加せず、元の H と通常商を保持する。

## 使われ方

旧 hpR 付きの完備性公開名を、同じ型から hpR だけを除いて提供する。
-/

@[expose] public noncomputable section PowerRootPrismMonicHodgeTateComplete

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (f : Polynomial A) (hf : f.Monic)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "Raw" => DeltaAdjoinDivision E dP a
local notation "dL" => deltaAdjoinDivisionMap E dP a dP
local notation "H" => PDCompletionH0 Raw p dL

include hf in
/-- 概要：無限根モニック実完備化の分母商は通常の意味でも p 完備。
方針：正次数では有界ねじれによる比較、次数零では零環の完備性を使う。
規約：標準分母像による元の通常商を使い、hpR と正次数を要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の prismatic 源の完備商。 -/
theorem powerRootPrismMonic_pdCompletion_hodgeTate_isAdicComplete :
    let := pdCompletionCommRing Raw p dL
    let T := H ⧸ Ideal.span {pdCompletionUnit Raw p dL dL}
    IsAdicComplete (Ideal.span {(p : T)}) T := by
  by_cases hz : f.natDegree = 0
  · let := pdCompletionCommRing Raw p dL
    let : Subsingleton H :=
      powerRootPrismMonic_pdCompletion_subsingleton_of_natDegree_zero W hW f hf hz
    infer_instance
  · exact powerRootPrismMonic_pdCompletion_hodgeTate_isAdicComplete_of_unconditional
      W hW f hf (Nat.pos_of_ne_zero hz)

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicHodgeTateComplete

/-! ## 元の実完備化を完全 δ 化した後の二元剰余

## 概要

元の無限根モニック実完備化を完全 δ 化し再完備化しても、標準二元導来剰余は離散で H⁰ は忠実平坦。
BS 著者版 Remark 7.15（著者版 p.62）の完全化後への平坦性の保存。

## 方針

完全 δ 基底での一般 Frobenius 段・余極限・実完備化の剰余判定に具体的入力を渡す。

基礎となる Hodge–Tate 商の完全忠実平坦性は、原典と異なる実源の純性による無条件版を使う。

## 規約

元の係数射・δ 構造を保持し、モニック性・正次数を明示し、prism 商の p 正則性は要求しない。

## 使われ方

最終 perfectoid 商の p 完全忠実平坦性を証明するための prism 側の入力。
-/

@[expose] public noncomputable section PowerRootPrismMonicPerfectionPairFaithful

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


local notation "c" => powerRootPrismMonicCompletionBaseMap W hW f
local notation "κ" => deltaAlgebraPerfectionCoefficient DH c
local notation "Cp" => DeltaPerfection DH
local notation "Hp" => PDCompletionH0 Cp p (κ W.generator)
local notation "t" => RingHom.comp (pdCompletionUnit Cp p (κ W.generator)) κ
local notation "M" => baseChangeScalarModule t
local notation "I" => Ideal.span {(p : A), W.generator}
local notation "Q" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q)
  (CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor M)
include hf hdeg

/-- 概要：完全 δ 化後の同じ実完備化の導来二元剰余の非零次数は消える。
方針：元の実完備化の導来剰余計算を一般の完全化剰余判定へ渡す。
規約：同じ標準係数射と明示仮定を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終商の完全忠実平坦性。 -/
theorem powerRootPrismMonicCompletedPerfection_pair_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    let := pdCompletionCommRing L p (jL dP)
    let := pdCompletionCommRing Cp p (κ W.generator)
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj (Y).obj) := by
  let := pdCompletionCommRing L p (jL dP)
  let := pdCompletionCommRing Cp p (κ W.generator)
  exact perfectPrismDeltaAlgebraPD_reduction_homology_isZero W DH c hW
    (powerRootPrismMonicCompletionBaseMap_isDeltaHom W hW f)
    (powerRootPrismMonicCompletion_pair_reduction_homology_isZero W hW f hf hdeg)
    (powerRootPrismMonicCompletion_pair_reductionH0_faithfullyFlat W hW f hf hdeg) i hi

/-- 概要：完全 δ 化後の同じ実完備化の導来二元剰余 H⁰ は忠実平坦。
方針：元の実完備化の導来剰余計算を一般の完全化剰余判定へ渡す。
規約：同じ標準係数射と明示仮定を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終商の完全忠実平坦性。 -/
theorem powerRootPrismMonicCompletedPerfection_pairH0_faithfullyFlat :
    let := pdCompletionCommRing L p (jL dP)
    let := pdCompletionCommRing Cp p (κ W.generator)
    Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj) := by
  let := pdCompletionCommRing L p (jL dP)
  let := pdCompletionCommRing Cp p (κ W.generator)
  exact perfectPrismDeltaAlgebraPD_reductionH0_faithfullyFlat W DH c hW
    (powerRootPrismMonicCompletionBaseMap_isDeltaHom W hW f)
    (powerRootPrismMonicCompletion_pair_reduction_homology_isZero W hW f hf hdeg)
    (powerRootPrismMonicCompletion_pair_reductionH0_faithfullyFlat W hW f hf hdeg)

/-- 概要：完全 δ 化後の同じ実完備化の標準係数加群は二元完全忠実平坦。
方針：元の実完備化の導来剰余計算を一般の完全化剰余判定へ渡す。
規約：同じ標準係数射と明示仮定を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終商の完全忠実平坦性。 -/
theorem powerRootPrismMonicCompletedPerfection_pair_completelyFaithfullyFlat :
    let := pdCompletionCommRing L p (jL dP)
    let := pdCompletionCommRing Cp p (κ W.generator)
    IsCompletelyFaithfullyFlat I (ModuleCat.carrier M) := by
  let := pdCompletionCommRing L p (jL dP)
  let := pdCompletionCommRing Cp p (κ W.generator)
  exact perfectPrismDeltaAlgebraPD_isCompletelyFaithfullyFlat W DH c hW
    (powerRootPrismMonicCompletionBaseMap_isDeltaHom W hW f)
    (powerRootPrismMonicCompletion_pair_reduction_homology_isZero W hW f hf hdeg)
    (powerRootPrismMonicCompletion_pair_reductionH0_faithfullyFlat W hW f hf hdeg)

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicPerfectionPairFaithful

/-! ## 元の無限根候補の完全化後商の p 完全忠実平坦性

## 概要

完全 δ 化・再完備化後の生成元商は、元の自然な基底射について p 完全忠実平坦。
BS 著者版 Remark 7.15（著者版 p.62）の一元根付き候補の平坦性。

## 方針

完全化後の分母正則性を完全 δ prism で確認し、正則主商の一般下降判定を使う。

基礎となる Hodge–Tate 商の完全忠実平坦性は、原典と異なる実源の純性による無条件版を使う。

## 規約

元の係数射と具体的候補を保持し、モニック性・正次数を明示し、prism 商の p 正則性は要求しない。
原典とは異なる Tor 底変換と完全 δ 化後の剰余判定の経路である。

## 使われ方

同じ最終 perfectoid 候補の整 perfectoid 性・根方程式と結び付ける。
-/

@[expose] public noncomputable section PowerRootPrismMonicPerfectionQuotientFaithful

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
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
local notation "v" => perfectPrismVarpi W hW
local notation "φ" => powerRootPrismMonicHodgeTateBaseMap W hW f



local notation "DL" => deltaAdjoinDivisionStructure E dP a
local notation "DH" => deltaPDCompletionStructure DL (jL dP)


local notation "c" => powerRootPrismMonicCompletionBaseMap W hW f
local notation "κ" => deltaAlgebraPerfectionCoefficient DH c
local notation "Cp" => DeltaPerfection DH
local notation "x" => deltaPerfectionOf DH 0 (uL (jL dP))
local notation "Hp" => PDCompletionH0 Cp p x
local notation "t" => RingHom.comp (pdCompletionUnit Cp p x) κ
local notation "M" => baseChangeScalarModule t
local notation "I" => Ideal.span {(p : A), W.generator}
local notation "Q" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q)
  (CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor M)
local notation "sC" => pdCompletionUnit Cp p x
local notation "T∞" => PDCompletionH0 Cp p x ⧸ Ideal.span {sC x}

/-- 概要：完全化後の実完備化の元の A 係数作用。
方針：標準完全化係数射から代数構造を取る。
規約：作用自体にモニック性・正次数は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の正則主商への下降。 -/
@[instance_reducible] def powerRootPrismMonicPerfectionAlgebra :
    let := pdCompletionCommRing L p (jL dP)
    let := pdCompletionCommRing Cp p x
    Algebra A Hp := by
  let := pdCompletionCommRing L p (jL dP)
  let := pdCompletionCommRing Cp p x
  exact (t).toAlgebra

/-- 概要：完全化後の実完備化では指定分母が正則。
方針：完全 δ 環の distinguished 元の実完備化の prism 性を使う。
規約：分母は元の標準係数射による像。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の生成元商の導来比較。 -/
theorem powerRootPrismMonicPerfection_generator_regular :
    let := pdCompletionCommRing L p (jL dP)
    let := pdCompletionCommRing Cp p x
    IsSMulRegular Hp (t W.generator) := by
  let := pdCompletionCommRing L p (jL dP)
  let := pdCompletionCommRing Cp p x
  have hk := deltaAlgebraPerfectionCoefficient_isDeltaHom W.deltaStructure DH c
    (powerRootPrismMonicCompletionBaseMap_isDeltaHom W hW f)
  have hd := hk.map_isDistinguished (W.isDistinguished_generator)
  exact (perfectDeltaPDPrism (deltaPerfectionStructure DH) (deltaPerfection_isPerfect DH)
    x hd).generator_regular

include hf hdeg in
/-- 概要：同じ完全化後 perfectoid 商の自然な基底射は p 完全忠実平坦。
方針：一般の δ 代数商判定に実剰余入力を渡し、標準係数射を代表元上で照合する。
規約：モニック性・正次数を仮定し、prism 商の p 正則性は要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の具体的根付き perfectoid 候補。 -/
theorem powerRootPrismMonicCompletedPerfectionBaseMap_completelyFaithfullyFlat :
    let := pdCompletionCommRing L p (jL dP)
    let := pdCompletionCommRing Cp p x
    let := (powerRootPrismMonicCompletedPerfectionBaseMap W hW f).toAlgebra
    IsCompletelyFaithfullyFlat (Ideal.span {(p : A ⧸ W.ideal)}) T∞ := by
  let := pdCompletionCommRing L p (jL dP)
  let G := DH
  let Cq := DeltaPerfection G
  let i := deltaPerfectionOf G 0
  let b := i (uL (jL dP))
  let := pdCompletionCommRing Cq p b
  have hb : deltaAlgebraPerfectionCoefficient G c W.generator = b := rfl
  let g := perfectedDeltaAlgebraQuotientBaseMap W G c b hb
  have hg : g = powerRootPrismMonicCompletedPerfectionBaseMap W hW f := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro r
    rfl
  have h := perfectedDeltaAlgebraQuotientBaseMap_completelyFaithfullyFlat W G c hW
    (powerRootPrismMonicCompletionBaseMap_isDeltaHom W hW f)
    (powerRootPrismMonicCompletion_pair_reduction_homology_isZero W hW f hf hdeg)
    (powerRootPrismMonicCompletion_pair_reductionH0_faithfullyFlat W hW f hf hdeg) b hb
  let F (qmap : (A ⧸ W.ideal) →+* T∞) :=
    let := qmap.toAlgebra
    IsCompletelyFaithfullyFlat (Ideal.span {(p : A ⧸ W.ideal)}) T∞
  have hF : F g := h
  exact Eq.mp (congrArg F hg) hF

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicPerfectionQuotientFaithful
