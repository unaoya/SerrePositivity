module

public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Unconditional.Source
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.CompletionPrism
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.InputUniversal
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientBaseChange
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.FrobeniusPullback
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Unconditional.Residue
public import SerrePositivity.BhattScholze.Andre.Variants.Auxiliary

/-!
# 自然な Frobenius テンソル上の pd 包

## 概要
Hodge–Tate 商への導来還元、Frobenius テンソル上の pd 包、追加の正則性なしの Frobenius 引戻しの pd 普遍性。
BS 著者版 Remark 7.15 の φ 引き戻しの計算に関わる、Frobenius テンソル上の分冪構造を構成する。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`PowerRootEnvelope/PerfectionFaithful`、`PowerRootEnvelope/VarpiComparison`、`Variants/MonicRootedExtension`。
-/

universe u w

/-! ## 元の Hodge–Tate 商への実導来還元

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の元の H/dH と、その自然な係数作用を保つ還元比較。

## 方針
分母正則性による実導来主商と通常の商を比較する。

## 規約
元の H を用い、hpR や別のねじれ除去商を導入しない。

## 使われ方
実残余 H⁰ の忠実平坦性を H/dH の p 完全忠実平坦性へ移す。
-/

@[expose] public noncomputable section PowerRootHodgeTateReduction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard

/-- 概要：指定した自然な主商射の作用で、通常係数拡大を同じ環商へ同定する。
方針：拡張イデアルの等式と代表元の公式で商環同型の線形性を示す。
規約：全係数の像を hφ で保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の H/dH の標準作用との照合。 -/
def unconditionalPrincipalScalarExtensionEquiv
    {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]
    (d : A) (s : S) (hs : algebraMap A S d = s)
    (φ : (A ⧸ Ideal.span {d}) →+* (S ⧸ Ideal.span {s}))
    (hφ : ∀ a : A, φ (Ideal.Quotient.mk (Ideal.span {d}) a) =
      Ideal.Quotient.mk (Ideal.span {s}) (algebraMap A S a)) :
    letI := (φ).toAlgebra
    ((ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {d}))).obj
      (ModuleCat.of A S)) ≃ₗ[A ⧸ Ideal.span {d}] (S ⧸ Ideal.span {s}) := by
  letI := (φ).toAlgebra
  let I := Ideal.span {d}
  let J := I.map (algebraMap A S)
  letI := adicQuotientAlgebra I S
  have hJ : J = Ideal.span {s} := by
    simp only [J, I, Ideal.map_span, Set.image_singleton, hs]
  let e := Ideal.quotEquivOfEq hJ
  let eL : (S ⧸ J) ≃ₗ[A ⧸ I] (S ⧸ Ideal.span {s}) :=
    { e.toAddEquiv with
      map_smul' := by
        intro a x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def]
        change e (Ideal.Quotient.mk J (algebraMap A S a) * Ideal.Quotient.mk J x) =
          φ (Ideal.Quotient.mk I a) * e (Ideal.Quotient.mk J x)
        rw [map_mul, Ideal.quotEquivOfEq_mk, Ideal.quotEquivOfEq_mk, hφ] }
  exact (quotientAlgebraScalarExtensionEquiv I S).trans eL

/-- 概要：生成元冪商の標準 mod p 還元の H⁰ は忠実平坦性を保つ。
方針：実ホモロジー比較と商環同型による係数制限で忠実平坦性を移す。
規約：実二生成剰余の同じ作用を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の Hodge–Tate 商の忠実性。 -/
theorem unconditionalGeneratorModPrimeH0_faithfullyFlat
    {A : Type u} [CommRing A] (p : ℕ) (d : A) (n : ℕ)
    (X : DerivedCategory.Minus (ModuleCat.{u} A))
    (hFF : Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), d ^ n})
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ Ideal.span {(p : A), d ^ n})) 0).obj
        ((boundedAboveDerivedBaseChange
          (Ideal.Quotient.mk (Ideal.span {(p : A), d ^ n}))).obj X).obj)) :
    let R := A ⧸ Ideal.span {d ^ n}
    Module.FaithfullyFlat (R ⧸ Ideal.span {(p : R)})
      ((DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {(p : R)})) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : R)}))).obj
          ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X)).obj) := by
  let Q := A ⧸ Ideal.span {(p : A), d ^ n}
  let R := A ⧸ Ideal.span {d ^ n}
  let S := R ⧸ Ideal.span {(p : R)}
  let e := prismaticGeneratorPowerModPEquiv p d n
  let M := (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
    ((boundedAboveDerivedBaseChange
      (Ideal.Quotient.mk (Ideal.span {(p : A), d ^ n}))).obj X).obj
  letI := e.toRingHom.toAlgebra
  letI : Module S M := Module.compHom M e.toRingHom
  letI : IsScalarTower S Q M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let eA : S ≃ₐ[S] Q := AlgEquiv.ofBijective (Algebra.ofId S Q) e.bijective
  have : Module.FaithfullyFlat S Q :=
    Module.FaithfullyFlat.of_linearEquiv S S eA.symm.toLinearEquiv
  have : Module.FaithfullyFlat Q M := hFF
  have : Module.FaithfullyFlat S M := Module.FaithfullyFlat.trans S Q M
  exact Module.FaithfullyFlat.of_linearEquiv S M
    (prismaticGeneratorPowerModPHomologyIso p d n X 0).toLinearEquiv

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "d" => W.generator
local notation "dP" => algebraMap A P d
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "c" => algebraMap A L
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "uL" => pdCompletionUnit L p (jL dP)
local notation "dH" => uL (jL dP)
local notation "T" => H ⧸ Ideal.span {dH}
local notation "R" => A ⧸ W.ideal
local notation "φ" => powerRootPrismMonicHodgeTateBaseMap W hW f
local notation "baseH" => powerRootPrismMonicCompletionBaseMap W hW f
local notation "XC" => PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional W hW f
local notation "M" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars c) (ModuleCat.of L H)

/-- 概要：元の実源の生成元商は、同じ H/dH の自然な R 作用の single と同型。
方針：実 H⁰ 比較、分母の正則性、通常主商の係数拡大比較を合成する。
規約：モニック正次数のみを要求し、元の H・分母像・係数射を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の Hodge–Tate 商の完全平坦性への移送。 -/
def powerRootPrismMonicHodgeTateDerivedReductionIso_of_unconditional
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    letI := pdCompletionCommRing L p (jL dP)
    letI := (φ).toAlgebra
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk W.ideal)).obj XC ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T) := by
  letI := pdCompletionCommRing L p (jL dP)
  letI := pdCompletionAlgebra L p (jL dP)
  letI := (baseH).toAlgebra
  letI := (φ).toAlgebra
  letI : IsScalarTower A L H := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [pairCompletion_algebraMap]
    rfl)
  let eM : M ≅ ModuleCat.of A H := by
    let e : ModuleCat.carrier M ≃ₗ[A] H :=
      { toFun := fun x => x
        invFun := fun x => x
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := by
          intro r x
          change H at x
          rw [RingHom.id_apply, ModuleCat.restrictScalars.smul_def]
          exact algebraMap_smul L r x }
    exact e.toModuleIso
  have hreg : IsSMulRegular H d := by
    have h := powerRootPrismMonicRaw_pdCompletion_generator_regular_of_unconditional W hW f hf hdeg
    change Function.Injective (fun x : H => dH * x) at h
    change Function.Injective (fun x : H => dH * x)
    exact h
  have hTor := scalarExtensionTorVanishing_principal_of_regular d W.generator_regular
    (ModuleCat.of A H) hreg
  let eQ := unconditionalPrincipalScalarExtensionEquiv d dH (by rfl) φ
    (powerRootPrismMonicHodgeTateBaseMap_mk W hW f)
  exact (boundedAboveDerivedBaseChange (Ideal.Quotient.mk W.ideal)).mapIso
      (powerRootPrismMonicSourcePDSingleIso_of_unconditional W hW f hf hdeg ≪≫
        boundedAboveDerivedSingleFunctor.mapIso eM) ≪≫
    boundedAboveDerivedBaseChangeModuleAugmentationIso
      (Ideal.Quotient.mk W.ideal) (ModuleCat.of A H) hTor ≪≫
    boundedAboveDerivedSingleFunctor.mapIso eQ.toModuleIso

local notation "HT" => boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)
local notation "qP" => Ideal.Quotient.mk (Ideal.span {(p : R)})
local notation "YT" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qP) HT

/-- 概要：元の H/dH の実 mod p 還元の非零次数は消える。
方針：元の源の二生成剰余を標準 mod p 還元へ比較し、作用を保つ分母商同型で移す。
規約：元の自然な R 作用を用い、hpR は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の p 完全平坦性の Tor 入力。 -/
theorem powerRootPrismMonicHodgeTateReduction_homology_isZero_of_unconditional
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (i : ℤ) (hi : i ≠ 0) :
    letI := pdCompletionCommRing L p (jL dP)
    letI := (φ).toAlgebra
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {(p : R)})) i).obj
      (YT).obj) := by
  letI := pdCompletionCommRing L p (jL dP)
  letI := (φ).toAlgebra
  have hd1 : d ^ (1 : ℕ) = d := pow_one _
  have hpair : IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat (A ⧸ Ideal.span {(p : A), d ^ 1})) i).obj
        ((boundedAboveDerivedBaseChange
          (Ideal.Quotient.mk (Ideal.span {(p : A), d ^ 1}))).obj XC).obj) := by
    rw [hd1]
    exact powerRootPrismMonicSourceIteratedPDResidue_homology_isZero_of_unconditional
      W hW f hf i hi
  have hz := prismaticGeneratorPowerModP_homology_isZero p d 1 XC i hpair
  rw [hd1] at hz
  let e := (boundedAboveDerivedBaseChange qP).mapIso
    (powerRootPrismMonicHodgeTateDerivedReductionIso_of_unconditional W hW f hf hdeg)
  exact hz.of_iso ((DerivedCategory.homologyFunctor
    (ModuleCat (R ⧸ Ideal.span {(p : R)})) i).mapIso
      (DerivedCategory.Minus.ι.mapIso e)).symm

/-- 概要：元の H/dH の実 mod p 還元の H⁰ は忠実平坦。
方針：A1-d の実剰余忠実平坦性を標準 mod p 比較と元の分母商比較へ渡す。
規約：追加の忠実平坦性仮定を残さない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の p 完全忠実平坦性の剰余入力。 -/
theorem powerRootPrismMonicHodgeTateReductionH0_faithfullyFlat_of_unconditional
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    letI := pdCompletionCommRing L p (jL dP)
    letI := (φ).toAlgebra
    Module.FaithfullyFlat (R ⧸ Ideal.span {(p : R)})
      ((DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {(p : R)})) 0).obj
        (YT).obj) := by
  letI := pdCompletionCommRing L p (jL dP)
  letI := (φ).toAlgebra
  have hd1 : d ^ (1 : ℕ) = d := pow_one _
  have hpair : Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), d ^ 1})
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ Ideal.span {(p : A), d ^ 1})) 0).obj
        ((boundedAboveDerivedBaseChange
          (Ideal.Quotient.mk (Ideal.span {(p : A), d ^ 1}))).obj XC).obj) := by
    rw [hd1]
    exact powerRootPrismMonicSourceIteratedPDResidueH0_faithfullyFlat_of_initialCoefficient W hW f
      (InitialCoefficient.sourceResidueH0_faithfullyFlat W hW f hf hdeg)
  have hFF := unconditionalGeneratorModPrimeH0_faithfullyFlat p d 1 XC hpair
  dsimp only at hFF
  rw [hd1] at hFF
  let N := (DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {(p : R)})) 0).obj
    ((boundedAboveDerivedBaseChange qP).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk W.ideal)).obj XC)).obj
  have : Module.FaithfullyFlat (R ⧸ Ideal.span {(p : R)}) N := hFF
  let e := (boundedAboveDerivedBaseChange qP).mapIso
    (powerRootPrismMonicHodgeTateDerivedReductionIso_of_unconditional W hW f hf hdeg)
  exact Module.FaithfullyFlat.of_linearEquiv (R ⧸ Ideal.span {(p : R)}) N
    ((DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {(p : R)})) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso e)).symm.toLinearEquiv

/-- 概要：元の自然な Hodge–Tate 商は p 完全忠実平坦。
方針：実 mod p 還元の離散性と忠実平坦性を標準 Tor・通常係数拡大へ移す。
規約：hpR・候補の p 正則性を仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の完全平坦性の無条件入力。 -/
theorem powerRootPrismMonicHodgeTate_prime_completelyFaithfullyFlat_of_unconditional
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    letI := pdCompletionCommRing L p (jL dP)
    letI := powerRootPrismMonicHodgeTateAlgebra W hW f
    IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T := by
  letI := pdCompletionCommRing L p (jL dP)
  letI := powerRootPrismMonicHodgeTateAlgebra W hW f
  let MT := ModuleCat.of R T
  have hTor : scalarExtensionTorVanishing qP MT := by
    apply (derivedModuleBaseChange_negative_homology_vanishes_iff qP MT).mp
    intro n hn
    exact (powerRootPrismMonicHodgeTateReduction_homology_isZero_of_unconditional
      W hW f hf hdeg (-(n : ℤ)) (by omega)).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {(p : R)}))
        (-(n : ℤ))).mapIso ((boundedAboveDerivedBaseChangeModuleNatIso qP).app MT)).symm
  have hFF : Module.FaithfullyFlat (R ⧸ Ideal.span {(p : R)})
      ((ModuleCat.extendScalars qP).obj MT) := by
    have : Module.FaithfullyFlat (R ⧸ Ideal.span {(p : R)})
        ((DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {(p : R)})) 0).obj
          (YT).obj) :=
      powerRootPrismMonicHodgeTateReductionH0_faithfullyFlat_of_unconditional W hW f hf hdeg
    exact Module.FaithfullyFlat.of_linearEquiv (R ⧸ Ideal.span {(p : R)})
      ((DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {(p : R)})) 0).obj (YT).obj)
      ((boundedAboveDerivedBaseChangeModuleH0Iso qP).app MT).symm.toLinearEquiv
  refine ⟨isCompletelyFlat_of_acyclic_flat_reduction (Ideal.span {(p : R)}) T hTor hFF.1, ?_⟩
  have := hFF
  let e := (quotientScalarExtensionEquiv (Ideal.span {(p : R)}) MT).trans
    (quotientTensorReductionEquiv (Ideal.span {(p : R)}) T).symm
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.symm

/-- 概要：元の H/dH の p 冪ねじれは有界。
方針：実生成元商の H⁰ の有界ねじれを、自然な R 線形比較で同じ通常商へ移す。
規約：p 正則性へ強めず、元の H/dH を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の通常 p 完備性の無条件入力。 -/
theorem powerRootPrismMonicHodgeTate_bounded_prime_torsion_of_unconditional
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    letI := pdCompletionCommRing L p (jL dP)
    ∃ N : ℕ, ∀ k : ℕ, ∀ x : T, (p : T) ^ k * x = 0 → (p : T) ^ N * x = 0 := by
  letI := pdCompletionCommRing L p (jL dP)
  letI := (φ).toAlgebra
  let Z := (boundedAboveDerivedBaseChange (Ideal.Quotient.mk W.ideal)).obj XC
  let e : ModuleCat.carrier ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj Z.obj) ≃ₗ[R] T :=
    ((DerivedCategory.homologyFunctor (ModuleCat R) 0).mapIso
    (DerivedCategory.Minus.ι.mapIso
      (powerRootPrismMonicHodgeTateDerivedReductionIso_of_unconditional W hW f hf hdeg)) ≪≫
    (realizedSingleH0Iso R).app (ModuleCat.of R T)).toLinearEquiv
  have hb := (powerRootPrismMonicSourceGeneratorPowerReduction_pure_bounded_of_unconditional
    W hW f 1 (by omega) hf hdeg).2.2
  have hd1 : d ^ (1 : ℕ) = d := pow_one _
  rw [hd1] at hb
  obtain ⟨N, hN⟩ := hb
  refine ⟨N, ?_⟩
  intro k x hx
  have hxR : (p : R) ^ k • x = 0 := by
    simpa only [Algebra.smul_def, map_pow, map_natCast] using hx
  have hz := hN k (e.symm x) (by rw [← e.symm.map_smul, hxR, map_zero])
  have ht := congrArg e hz
  simpa only [map_smul, map_zero, LinearEquiv.apply_symm_apply, Algebra.smul_def,
    map_pow, map_natCast] using ht

/-- 概要：元の H/dH は通常の意味でも p 完備。
方針：同じ通常商の有界 p ねじれと導来完備性の既存比較を使う。
規約：候補の p 正則性を要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の prism 源の初期性への入力。 -/
theorem powerRootPrismMonic_pdCompletion_hodgeTate_isAdicComplete_of_unconditional
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    letI := pdCompletionCommRing L p (jL dP)
    IsAdicComplete (Ideal.span {(p : T)}) T := by
  letI := pdCompletionCommRing L p (jL dP)
  exact powerRootPrismMonicSourceQuotient_complete_of_bounded W hW f
    (powerRootPrismMonicHodgeTate_bounded_prime_torsion_of_unconditional W hW f hf hdeg)

end SerrePositivity.BhattScholze.Andre

end PowerRootHodgeTateReduction

/-! ## 自然な実 Frobenius テンソル上の実 pd 包

## 概要

根変数上で自然性を確認した実テンソルに、元の mod p 入力の実分冪構造と pd 普遍性を与える。
BS 著者版 Remark 7.15(1)（著者版 p.62）の入力環上の構造比較。

## 方針

同じ無限根環上の実代数同型に沿って、正次数イデアル・分冪構造・普遍性を戻す。
原典とは異なり、Witt 座標による半線形比較と通常テンソルを経て実分冪構造を移送する。

## 規約

完全 prism とモニック性のみを仮定する。絶対 prismatic 源の同定はまだ主張しない。

## 使われ方

元の自然な T/ϖ の係数 Frobenius テンソルを、自然な入力環作用を持つ pd 包として扱う。
-/

@[expose] public noncomputable section FrobeniusTensorPD

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open scoped TensorProduct
open SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
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
local notation "R" => A ⧸ W.ideal
local notation "v" => perfectPrismVarpi W hW
local notation "Iv" => Ideal.span {v}
local notation "Rv" => R ⧸ Iv
local notation "S" => H ⧸ Ideal.span {dH, xH}
local notation "φ" => powerRootPrismMonicHodgeTateBaseMap W hW f

local notation "Rp" => R ⧸ Ideal.span {(p : R)}
local notation "Np" => PowerRootPolynomial Rp p hp
local notation "bp" => RingHom.comp (Ideal.Quotient.mk (Ideal.span {(p : R)}))
  (Ideal.Quotient.mk (OrientedPrism.ideal W))
local notation "zp" => powerRootPolynomialBaseMap Rp p hp (Polynomial.map bp f)
local notation "Dp" => PrincipalDPPresentation Np zp
local notation "evp" => perfectPrismVarpiFrobeniusQuotientEquiv W hW
local notation "Mv" => T ⧸ Ideal.map φ Iv

local notation "Ft" => Rp ⊗[Rv] Mv
local notation "Et" => powerRootPrismMonicVarpiFrobeniusBaseChangeAlgEquiv W hW f

variable (hf : f.Monic)
local notation "Ein" => powerRootPrismMonicFrobeniusTensorInputAlgEquiv W hW f hf

/-- 概要：自然な実テンソル上に元の mod p 入力の実分冪構造を与える。
方針：係数を保つ実同型に沿って比較先の構造を戻す。
規約：射影的商を使い、prism 商の p 正則性を仮定しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 包の構造。 -/
def powerRootPrismMonicFrobeniusTensorDividedPowers_of_unconditional
    :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := (evp).toRingHom.toAlgebra
    let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
    DividedPowers (powerRootPrismMonicFrobeniusTensorPDIdeal W hW f hf) := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := (evp).toRingHom.toAlgebra
  let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
  exact principalPDSourceDividedPowers zp Ein
    (powerRootPrimeFrobeniusDividedPowers_of_unconditional W hW f hf)

/-- 概要：実テンソル比較は元の実分冪構造を比較先へ保つ。
方針：同型の源へ戻した構造の分冪射性を使う。
規約：同じ入力環作用と同じイデアルを使う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 比較。 -/
theorem powerRootPrismMonicFrobeniusTensorInputAlgEquiv_isDPMorphism_of_unconditional
    :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := (evp).toRingHom.toAlgebra
    let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
    (powerRootPrismMonicFrobeniusTensorDividedPowers_of_unconditional W hW f hf).IsDPMorphism
      (powerRootPrimeFrobeniusDividedPowers_of_unconditional W hW f hf) (Ein).toRingHom := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := (evp).toRingHom.toAlgebra
  let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
  exact principalPDSourceEquiv_isDPMorphism zp Ein
    (powerRootPrimeFrobeniusDividedPowers_of_unconditional W hW f hf)

/-- 概要：自然な入力元の全分冪は標準分冪生成元の実同型による逆像。
方針：比較先の標準分冪値を係数を保つ同型で戻す。
規約：零次数を含む全次数 n を指定する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実分冪値の同定。 -/
theorem powerRootPrismMonicFrobeniusTensorDividedPowers_input_apply_of_unconditional
    (n : ℕ) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := (evp).toRingHom.toAlgebra
    let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
    (powerRootPrismMonicFrobeniusTensorDividedPowers_of_unconditional W hW f hf).dpow n
      (algebraMap Np Ft zp) = (Ein).symm (principalDPGenerator zp n) := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := (evp).toRingHom.toAlgebra
  let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
  exact principalPDSourceDividedPowers_base_apply zp Ein
    (powerRootPrimeFrobeniusDividedPowers_of_unconditional W hW f hf)
    (powerRootPrimeFrobeniusDividedPowers_base_apply_of_unconditional W hW f hf) n

/-- 概要：自然な実 Frobenius テンソルは元の mod p 入力の pd 包の普遍性を持つ。
方針：同じ入力環上の代数同型で標準主分冪包の普遍性を移す。
原典とは異なる半線形比較・通常テンソル・実分冪構造の移送による証明。
規約：標的の宇宙・ねじれ・完備性は制約しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実引戻し側の pd 包性。 -/
theorem existsUnique_powerRootPrismMonicFrobeniusTensorPDMorphism_of_unconditional
    {B : Type w} [CommRing B] [Algebra Np B] {I : Ideal B}
    (Ht : DividedPowers I) (hzB : algebraMap Np B zp ∈ I) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := (evp).toRingHom.toAlgebra
    let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
    ∃! F : Ft →ₐ[Np] B,
      (powerRootPrismMonicFrobeniusTensorDividedPowers_of_unconditional W hW f hf).IsDPMorphism
        Ht F.toRingHom := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := (evp).toRingHom.toAlgebra
  let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
  exact existsUnique_principalPDSourceMorphism zp Ein
    (powerRootPrimeFrobeniusDividedPowers_of_unconditional W hW f hf)
    (powerRootPrimeFrobeniusDividedPowers_base_apply_of_unconditional W hW f hf) Ht hzB

end SerrePositivity.BhattScholze.Andre

end FrobeniusTensorPD

/-! ## 追加正則性なしの実 Frobenius 引戻しの pd 普遍性

## 概要

A 全体の自然な実 Frobenius 引戻しは、モニック性のみの下で元の mod p 入力の実 pd 包となる。
BS 著者版 Remark 7.15(1)（著者版 p.62）の φ_A 引戻しの pd 比較から prism 商の p 正則性を除く。

## 方針

射影的な正次数商を使って構成した比較先の実分冪構造を、検証済みの自然な入力環同型で戻す。
原典とは異なる線形切断・半線形比較・通常テンソル・実分冪構造の移送による証明。

## 規約

完全 prism とモニック性のみを要求する。原典の係数表記との最終照合と絶対 prismatic 源の同定は別工程。

## 使われ方

実 Frobenius 引戻しそのものから、追加正則性なしに任意の分冪標的への一意な射を得る。
-/

@[expose] public noncomputable section FullFrobeniusPD

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open scoped TensorProduct
open SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
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
local notation "R" => A ⧸ W.ideal
local notation "v" => perfectPrismVarpi W hW
local notation "Iv" => Ideal.span {v}
local notation "Rv" => R ⧸ Iv
local notation "S" => H ⧸ Ideal.span {dH, xH}
local notation "φ" => powerRootPrismMonicHodgeTateBaseMap W hW f

local notation "Rp" => R ⧸ Ideal.span {(p : R)}
local notation "Np" => PowerRootPolynomial Rp p hp
local notation "bp" => RingHom.comp (Ideal.Quotient.mk (Ideal.span {(p : R)}))
  (Ideal.Quotient.mk (OrientedPrism.ideal W))
local notation "zp" => powerRootPolynomialBaseMap Rp p hp (Polynomial.map bp f)
local notation "Dp" => PrincipalDPPresentation Np zp
local notation "evp" => perfectPrismVarpiFrobeniusQuotientEquiv W hW
local notation "Mv" => T ⧸ Ideal.map φ Iv

local notation "bv" => RingHom.comp (Ideal.Quotient.mk Iv) (Ideal.Quotient.mk W.ideal)
local notation "frob" => DeltaStructure.frobeniusEquiv W.deltaStructure hW
local notation "Ac" => TensorBaseCopy A
local notation "downA" => RingEquiv.toRingHom (tensorBaseCopyRingEquiv A)
local notation "αc" => RingEquiv.trans frob (RingEquiv.symm (tensorBaseCopyRingEquiv A))
local notation "rA" => RingHom.comp (algebraMap Rp Dp) bp
local notation "U" => powerRootPrismMonicVarpiFrobeniusResidueEquiv W hW f

local notation "qA" => powerRootPrismMonicVarpiBaseMap W hW f
local notation "At" => Ac ⊗[A] Mv
local notation "Ef" => powerRootPrismMonicFullFrobeniusPullbackAlgEquiv W hW f

variable (hf : f.Monic)
local notation "Ein" => powerRootPrismMonicFullFrobeniusInputAlgEquiv W hW f hf

/-- 概要：自然な A 全体の実引戻し上に元の mod p 入力の実分冪構造を与える。
方針：係数を保つ実同型に沿って比較先の構造を戻す。
規約：prism 商の p 正則性・正次数を仮定しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 包の構造。 -/
def powerRootPrismMonicFullFrobeniusDividedPowers_of_unconditional :
    let := pdCompletionCommRing L p (jL dP)
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
    DividedPowers (powerRootPrismMonicFullFrobeniusPDIdeal W hW f hf) := by
  let := pdCompletionCommRing L p (jL dP)
  let := (qA).toAlgebra
  let := (RingHom.comp rA downA).toAlgebra
  let := (αc).toRingHom.toAlgebra
  let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
  exact principalPDSourceDividedPowers zp Ein
    (powerRootPrimeFrobeniusDividedPowers_of_unconditional W hW f hf)

/-- 概要：A 全体の実引戻し比較は元の実分冪構造を比較先へ保つ。
方針：同型の源へ戻した構造の分冪射性を使う。
規約：同じ入力環作用と同じイデアルを使う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 比較。 -/
theorem powerRootPrismMonicFullFrobeniusInputAlgEquiv_isDPMorphism_of_unconditional :
    let := pdCompletionCommRing L p (jL dP)
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
    (powerRootPrismMonicFullFrobeniusDividedPowers_of_unconditional W hW f hf).IsDPMorphism
      (powerRootPrimeFrobeniusDividedPowers_of_unconditional W hW f hf) (Ein).toRingHom := by
  let := pdCompletionCommRing L p (jL dP)
  let := (qA).toAlgebra
  let := (RingHom.comp rA downA).toAlgebra
  let := (αc).toRingHom.toAlgebra
  let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
  exact principalPDSourceEquiv_isDPMorphism zp Ein
    (powerRootPrimeFrobeniusDividedPowers_of_unconditional W hW f hf)

/-- 概要：自然な入力元の全分冪は標準分冪生成元の実同型による逆像。
方針：比較先の標準分冪値を係数を保つ同型で戻す。
規約：零次数を含む全次数 n を指定する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実分冪値の同定。 -/
theorem powerRootPrismMonicFullFrobeniusDividedPowers_input_apply_of_unconditional
    (n : ℕ) :
    let := pdCompletionCommRing L p (jL dP)
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
    (powerRootPrismMonicFullFrobeniusDividedPowers_of_unconditional W hW f hf).dpow n
      (algebraMap Np At zp) = (Ein).symm (principalDPGenerator zp n) := by
  let := pdCompletionCommRing L p (jL dP)
  let := (qA).toAlgebra
  let := (RingHom.comp rA downA).toAlgebra
  let := (αc).toRingHom.toAlgebra
  let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
  exact principalPDSourceDividedPowers_base_apply zp Ein
    (powerRootPrimeFrobeniusDividedPowers_of_unconditional W hW f hf)
    (powerRootPrimeFrobeniusDividedPowers_base_apply_of_unconditional W hW f hf) n

/-- 概要：自然な実 Frobenius テンソルは元の mod p 入力の pd 包の普遍性を持つ。
方針：同じ入力環上の代数同型で標準主分冪包の普遍性を移す。
原典とは異なる半線形比較・通常テンソル・実分冪構造の移送による証明。
規約：標的の宇宙・ねじれ・完備性は制約しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実引戻し側の pd 包性。 -/
theorem existsUnique_powerRootPrismMonicFullFrobeniusPDMorphism_of_unconditional
    {B : Type w} [CommRing B] [Algebra Np B] {I : Ideal B}
    (Ht : DividedPowers I) (hzB : algebraMap Np B zp ∈ I) :
    let := pdCompletionCommRing L p (jL dP)
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
    ∃! F : At →ₐ[Np] B,
      (powerRootPrismMonicFullFrobeniusDividedPowers_of_unconditional W hW f hf).IsDPMorphism
        Ht F.toRingHom := by
  let := pdCompletionCommRing L p (jL dP)
  let := (qA).toAlgebra
  let := (RingHom.comp rA downA).toAlgebra
  let := (αc).toRingHom.toAlgebra
  let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
  exact existsUnique_principalPDSourceMorphism zp Ein
    (powerRootPrimeFrobeniusDividedPowers_of_unconditional W hW f hf)
    (powerRootPrimeFrobeniusDividedPowers_base_apply_of_unconditional W hW f hf) Ht hzB

end SerrePositivity.BhattScholze.Andre

end FullFrobeniusPD
