module

public import SerrePositivity.BhattScholze.Andre.PerfectPrismMonicQuotientReduction
public import SerrePositivity.BhattScholze.PrismaticGeneratorPowerModPFaithful

/-!
# André E1・E2：有限モニック族の標準 perfectoid 候補の p 完全忠実平坦性

## 概要

完全 prism 上の有限正次数モニック族の既存 perfectoid 候補の標準 A/d 基底射は p 完全忠実平坦。
BS Thm 7.14（著者版 p.61）、Rem 7.15（p.62）の有限根付き候補。

## 方針

生成元商の実還元を標準候補の single と同定し、prism 側の (p,d) 剰余の Tor 消滅と
忠実平坦性を正確な標準 mod p 商へ移す。原典の Prop 7.11 を使う経路とは異なる計算。

## 規約

モニック性と正次数、有限全列挙を明示する。任意族への最終接続は別工程。

## 使われ方

既存の根方程式と整 perfectoid 性を合わせ、有限モニック族の根付き拡大を公開する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (f : σ → Polynomial A)
variable (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
variable {m : ℕ} (eσ : Fin m ≃ σ)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "hd" => OrientedPrism.isDistinguished_of_perfect P hP
local notation "φ" => polynomialPrismCoefficientMap D d f
local notation "M" => baseChangeScalarModule φ
local notation "X" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor M
local notation "J" => Ideal.span {d}
local notation "R" => A ⧸ J
local notation "q" => Ideal.Quotient.mk J
local notation "I" => Ideal.span {(p : A), d}
local notation "Q" => A ⧸ I
local notation "q₀" => Ideal.Quotient.mk I
local notation "g" => polynomialPerfectoidCandidateBaseMap D d f hd
local notation "N" => baseChangeScalarModule g
local notation "K" => Ideal.span {(p : R)}
local notation "Qp" => R ⧸ K
local notation "qp" => Ideal.Quotient.mk K
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qp)
  (Functor.obj boundedAboveDerivedSingleFunctor N)
include hP hf hdeg eσ

/-- 概要：既存多項式 prismの同じ(p,d)実還元の非零次数は消える。
方針：標準生成元商と mod p 商の実合成比較に、prism 側の実剰余入力を移す。
規約：完全 prism 上の有限正次数モニック族と同じ標準基底射を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の根付き perfectoid 候補の p 完全忠実平坦性。 -/
theorem perfectPrismMonicPrism_pair_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    letI := polynomialPrismCommRing D d f
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj
      ((boundedAboveDerivedBaseChange q₀).obj X).obj) := by
  let := polynomialPrismCommRing D d f
  let e := boundedAboveDerivedBaseChangeModuleAugmentationIso q₀ M
    (perfectPrismMonicPrism_torVanishing P hP f hf hdeg eσ)
  exact (derivedSingleHomology_isZero ((ModuleCat.extendScalars q₀).obj M) i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat Q) i).mapIso
      (DerivedCategory.Minus.ι.mapIso e))

/-- 概要：同じ多項式 prismの実(p,d)還元のH0は忠実平坦。
方針：標準生成元商と mod p 商の実合成比較に、prism 側の実剰余入力を移す。
規約：完全 prism 上の有限正次数モニック族と同じ標準基底射を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の根付き perfectoid 候補の p 完全忠実平坦性。 -/
theorem perfectPrismMonicPrism_pairH0_faithfullyFlat :
    letI := polynomialPrismCommRing D d f
    Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange q₀).obj X).obj) := by
  let := polynomialPrismCommRing D d f
  let : Module.FaithfullyFlat Q ((ModuleCat.extendScalars q₀).obj M) :=
    perfectPrismMonicPrism_scalarExtension_faithfullyFlat P hP f hf hdeg eσ
  exact Module.FaithfullyFlat.of_linearEquiv Q ((ModuleCat.extendScalars q₀).obj M)
    ((boundedAboveDerivedBaseChangeModuleH0Iso q₀).app M).toLinearEquiv

/-- 概要：perfectoid商の標準基底射の実mod p還元の非零次数は消える。
方針：標準生成元商と mod p 商の実合成比較に、prism 側の実剰余入力を移す。
規約：完全 prism 上の有限正次数モニック族と同じ標準基底射を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の根付き perfectoid 候補の p 完全忠実平坦性。 -/
theorem perfectPrismMonicPerfectoid_modP_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    letI := polynomialPrismCommRing D d f
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Qp) i).obj (Y).obj) := by
  let := polynomialPrismCommRing D d f
  have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat Qp) i).obj
      ((boundedAboveDerivedBaseChange qp).obj ((boundedAboveDerivedBaseChange q).obj X)).obj) := by
    let HQ (a : A) := IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat (A ⧸ Ideal.span {(p : A), a})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), a}))).obj X).obj)
    have hq0 : HQ d := perfectPrismMonicPrism_pair_homology_isZero P hP f hf hdeg eσ i hi
    have hq1 : HQ (d ^ 1) := Eq.mp (congrArg HQ (_root_.pow_one d).symm) hq0
    let HW (a : A) := IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat ((A ⧸ Ideal.span {a}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {a})})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk
          (Ideal.span {(p : A ⧸ Ideal.span {a})}))).obj
            ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X)).obj)
    have hw1 : HW (d ^ 1) := prismaticGeneratorPowerModP_homology_isZero p d 1 X i hq1
    exact Eq.mp (congrArg HW (_root_.pow_one d)) hw1
  exact hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat Qp) i).mapIso
    (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange qp).mapIso
      (perfectPrismMonicPrism_derivedQuotientIso P hP f)))).symm

/-- 概要：同じ実mod p還元のH0は、正確な基底剰余環上で忠実平坦。
方針：標準生成元商と mod p 商の実合成比較に、prism 側の実剰余入力を移す。
規約：完全 prism 上の有限正次数モニック族と同じ標準基底射を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の根付き perfectoid 候補の p 完全忠実平坦性。 -/
theorem perfectPrismMonicPerfectoid_modPH0_faithfullyFlat :
    letI := polynomialPrismCommRing D d f
    Module.FaithfullyFlat Qp ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).obj (Y).obj) := by
  let := polynomialPrismCommRing D d f
  let W := (boundedAboveDerivedBaseChange qp).obj ((boundedAboveDerivedBaseChange q).obj X)
  let : Module.FaithfullyFlat Qp
      ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).obj W.obj) := by
    let HQ (a : A) := Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), a})
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ Ideal.span {(p : A), a})) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), a}))).obj X).obj)
    have hq0 : HQ d := perfectPrismMonicPrism_pairH0_faithfullyFlat P hP f hf hdeg eσ
    have hq1 : HQ (d ^ 1) := Eq.mp (congrArg HQ (_root_.pow_one d).symm) hq0
    let HW (a : A) := Module.FaithfullyFlat
      ((A ⧸ Ideal.span {a}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {a})})
      ((DerivedCategory.homologyFunctor
        (ModuleCat ((A ⧸ Ideal.span {a}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {a})})) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk
          (Ideal.span {(p : A ⧸ Ideal.span {a})}))).obj
            ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X)).obj)
    have hw1 : HW (d ^ 1) := prismaticGeneratorPowerModPH0_faithfullyFlat p d 1 X hq1
    exact Eq.mp (congrArg HW (_root_.pow_one d)) hw1
  exact Module.FaithfullyFlat.of_linearEquiv Qp
    ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).obj W.obj)
    ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange qp).mapIso
        (perfectPrismMonicPrism_derivedQuotientIso P hP f)))).toLinearEquiv.symm

/-- 概要：同じperfectoid商の基底係数加群の高次mod p Torは零。
方針：標準生成元商と mod p 商の実合成比較に、prism 側の実剰余入力を移す。
規約：完全 prism 上の有限正次数モニック族と同じ標準基底射を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の根付き perfectoid 候補の p 完全忠実平坦性。 -/
theorem perfectPrismMonicPerfectoid_torVanishing :
    letI := polynomialPrismCommRing D d f
    scalarExtensionTorVanishing qp N := by
  let := polynomialPrismCommRing D d f
  apply (derivedModuleBaseChange_negative_homology_vanishes_iff qp N).mp
  intro n hn
  exact (perfectPrismMonicPerfectoid_modP_homology_isZero
    P hP f hf hdeg eσ (-(n : ℤ)) (by omega)).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat Qp) (-(n : ℤ))).mapIso
      ((boundedAboveDerivedBaseChangeModuleNatIso qp).app N)).symm

/-- 概要：同じperfectoid商の通常mod p係数拡大は忠実平坦。
方針：標準生成元商と mod p 商の実合成比較に、prism 側の実剰余入力を移す。
規約：完全 prism 上の有限正次数モニック族と同じ標準基底射を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の根付き perfectoid 候補の p 完全忠実平坦性。 -/
theorem perfectPrismMonicPerfectoid_scalarExtension_faithfullyFlat :
    letI := polynomialPrismCommRing D d f
    Module.FaithfullyFlat Qp ((ModuleCat.extendScalars qp).obj N) := by
  let := polynomialPrismCommRing D d f
  let : Module.FaithfullyFlat Qp
      ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).obj (Y).obj) :=
    perfectPrismMonicPerfectoid_modPH0_faithfullyFlat P hP f hf hdeg eσ
  exact Module.FaithfullyFlat.of_linearEquiv Qp
    ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).obj (Y).obj)
    ((boundedAboveDerivedBaseChangeModuleH0Iso qp).app N).toLinearEquiv.symm

/-- 概要：有限正次数モニック族のperfectoid候補の標準基底射はp完全忠実平坦。
方針：標準生成元商と mod p 商の実合成比較に、prism 側の実剰余入力を移す。
規約：完全 prism 上の有限正次数モニック族と同じ標準基底射を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の根付き perfectoid 候補の p 完全忠実平坦性。 -/
theorem perfectPrismMonicPerfectoid_isCompletelyFaithfullyFlat :
    letI := polynomialPrismCommRing D d f
    IsCompletelyFaithfullyFlat K (ModuleCat.carrier N) := by
  let := polynomialPrismCommRing D d f
  let Nc : ModuleCat.{u} R := N
  have hff : Module.FaithfullyFlat Qp ((ModuleCat.extendScalars qp).obj Nc) :=
    perfectPrismMonicPerfectoid_scalarExtension_faithfullyFlat P hP f hf hdeg eσ
  refine ⟨isCompletelyFlat_of_acyclic_flat_reduction K Nc
    (perfectPrismMonicPerfectoid_torVanishing P hP f hf hdeg eσ) hff.1, ?_⟩
  let e := (quotientScalarExtensionEquiv K Nc).trans (quotientTensorReductionEquiv K Nc).symm
  let := hff
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.symm

/-- 概要：有限正次数モニック族の既存 perfectoid 候補の標準基底射は p 完全忠実平坦。
方針：制限加群の完全忠実平坦性を、同じ環射の toAlgebra の作用と恒等線形同型で照合する。
規約：基底環は元の A/d、係数射は候補構成の標準射を使う。
使われ方：BS Thm 7.14（著者版 p.61）、Rem 7.15（p.62）の有限根付き拡大。 -/
theorem perfectPrismMonicPerfectoidBaseMap_isCompletelyFaithfullyFlat :
    letI := polynomialPrismCommRing D d f
    letI := (g).toAlgebra
    IsCompletelyFaithfullyFlat K (PolynomialPerfectoidCandidate D d f hd) := by
  let := polynomialPrismCommRing D d f
  have hN := perfectPrismMonicPerfectoid_isCompletelyFaithfullyFlat P hP f hf hdeg eσ
  let := (g).toAlgebra
  let e : N ≃ₗ[R] PolynomialPerfectoidCandidate D d f hd :=
    { toFun := fun y => y
      invFun := fun y => y
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a y
        rw [RingHom.id_apply, ModuleCat.restrictScalars.smul_def] }
  exact isCompletelyFaithfullyFlat_of_linearEquiv K e hN

end SerrePositivity.BhattScholze.Andre
