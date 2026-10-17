module

public import SerrePositivity.BhattScholze.Andre.CompletelyFlatRegularAlgebraReduction
public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicCompletionUniversal
public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicHodgeTateCompletelyFaithfullyFlat
public import SerrePositivity.HomologicalAlgebra.TorAlgebraAcyclicBaseChange
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete

/-!
# André E1・E2：元の無限根モニック実完備化の二元完全平坦性

## 概要

元の実完備化 H は、元の完全 prism の係数作用について (p,d) 完全平坦。
BS Rem 7.15（著者版 p.62）の δ 完全化に渡す導来剰余の計算。

## 方針

自然な H/d の係数作用と標準主環商の作用を照合し、d の正則性から p 完全平坦性を戻す。

## 規約

元の実 H⁰ と標準係数射を保持する。prism 商の p 正則性・モニック性・正次数を明示する。

## 使われ方

元の H の導来 (p,d) 剰余を δ 完全化の一般剰余判定へ渡す。
-/

@[expose] public noncomputable section
universe u
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
open SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal))
variable (f : Polynomial A) (hf : f.Monic) (hdeg : 0 < f.natDegree)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
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
使われ方：BS Rem 7.15（著者版 p.62）の元の A 作用での導来剰余。 -/
@[instance_reducible] def powerRootPrismMonicCompletionAlgebra :
    let := pdCompletionCommRing L p (jL dP)
    Algebra A H := by
  let := pdCompletionCommRing L p (jL dP)
  exact (powerRootPrismMonicCompletionBaseMap W hW f).toAlgebra

/-- 概要：H/d の自然な基底商作用は標準主環商の作用と一致する。
方針：商基底の元を A の代表元へ戻して標準係数射を照合する。
規約：同じ実完備化の同じ分母商を使う。
使われ方：BS Rem 7.15（著者版 p.62）の正則主剰余判定の係数作用。 -/
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

include hpR hf hdeg in
/-- 概要：元の無限根モニック実完備化は (p,d) 完全平坦。
方針：分母正則性と標準作用に移した H/d の p 完全平坦性を一般判定へ渡す。
規約：元の A 係数作用と実 H⁰ を用いる。
使われ方：BS Rem 7.15（著者版 p.62）の完全 δ 化の導来剰余入力。 -/
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
    exact (powerRootPrismMonicHodgeTate_prime_completelyFaithfullyFlat W hW hpR f hf hdeg).1
  apply completelyFlat_pair_algebra_of_regular_reduction (p : A) W.generator
    W.generator_regular H hreg
  simpa only [map_natCast] using hred

/-- 概要：標準係数射で制限した加群は元の自然な A 代数と線形同型。
方針：制限スカラー加群と代数作用の標準比較を使う。
規約：元の実完備化の係数射を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の導来底変換への入力。 -/
def powerRootPrismMonicCompletionScalarEquiv :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicCompletionAlgebra W hW f
    baseChangeScalarModule (powerRootPrismMonicCompletionBaseMap W hW f) ≃ₗ[A] H := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicCompletionAlgebra W hW f
  exact baseChangeScalarAlgebraEquiv (B := H)

include hpR hf hdeg in
/-- 概要：元の実完備化の (p,d) 標準底変換の高次 Tor は零。
方針：二元完全平坦性を標準剰余係数加群へ適用する。
規約：標準係数作用を持つ加群そのものを使う。
使われ方：BS Rem 7.15（著者版 p.62）の導来剰余の離散性。 -/
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
    (powerRootPrismMonicCompletion_pair_completelyFlat W hW hpR f hf hdeg)

include hpR hf hdeg in
/-- 概要：元の実完備化の導来 (p,d) 剰余は非零次数で消える。
方針：高次 Tor の消滅から標準増大同型を作り、単項複体のホモロジーを使う。
規約：標準係数射で制限した実加群の導来底変換を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の δ 完全化の剰余計算。 -/
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
    (powerRootPrismMonicCompletion_pair_scalarExtensionTorVanishing W hW hpR f hf hdeg)
  exact (derivedSingleHomology_isZero ((ModuleCat.extendScalars q).obj M) i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat _) i).mapIso
      (DerivedCategory.Minus.ι.mapIso e))

end SerrePositivity.BhattScholze.Andre
