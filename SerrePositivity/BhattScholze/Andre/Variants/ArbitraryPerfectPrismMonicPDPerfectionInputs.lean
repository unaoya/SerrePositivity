module

public import SerrePositivity.BhattScholze.Andre.PerfectPrismMonicPDPerfectionInputs
public import SerrePositivity.BhattScholze.Andre.Variants.ArbitraryPerfectPrismMonicRawPDCompletelyFlat

/-!
# André E1・E2（任意族）：raw モニック PD 環の δ 完全化への平坦性入力

## 概要

完全 prism 上の任意正次数モニック族の raw PD 環の標準係数射は δ 射で、
その δ 完全化の実 PD 完備化は元の (p,d) に関して完全忠実平坦。
BS Rem 7.15（著者版 p.62）の最終完全 prism 候補への準備。

## 方針

raw PD 環の元の係数制限作用を標準環射の作用に同定し、既存の一般 δ 代数の定理を適用する。
原典の Prop 7.11 を使う経路とは異なる具体的な係数射の計算。

## 規約

完全化の対象は明示的に固定する。最終 f/d 候補との環比較と perfectoid 商は別工程。

## 使われ方

一般の完備化・δ 完全化の比較同型を介して、最終根付き候補へ完全忠実平坦性を移す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]

section Perfect
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (f : σ → Polynomial A)
variable (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun t : σ => monicRelation (f t) t)
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "F" => deltaAdjoinDivisionStructure E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "z" => (c d)
local notation "B" => PDCompletionH0 Raw p z
local notation "G" => deltaPDCompletionStructure F z
local notation "s" => pdCompletionUnit Raw p z
local notation "j" => RingHom.comp s c
local notation "M" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars c) (ModuleCat.of Raw B)
local notation "I" => Ideal.span {(p : A), d}
local notation "Q" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q)
  (Functor.obj boundedAboveDerivedSingleFunctor (baseChangeScalarModule j))

include hP hf hdeg

/-- 概要：完全prism上では、同じPD係数射に沿う実還元の非零次数は消える。
方針：raw PD 環の元の係数作用を標準環射の作用に同定し、一般 δ 完全化の定理へ渡す。
規約：係数作用の比較自体にはモニック性は不要。完全 prism 上の適用には任意正次数モニック族を使う。
使われ方：BS Rem 7.15（著者版 p.62）の最終完全 prism 候補への移送。 -/
theorem perfectPrismMonicPDSource_reduction_homology_isZero_arbitrary (i : ℤ) (hi : i ≠ 0) :
    letI := pdCompletionCommRing Raw p z
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj (Y).obj) := by
  let := pdCompletionCommRing Raw p z
  have hz := perfectPrismMonicRawPD_reduction_homology_isZero_arbitrary P hP f hf hdeg  i hi
  exact hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat Q) i).mapIso
    (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange q).mapIso
      (boundedAboveDerivedSingleFunctor.mapIso (monicPrismaticPDSourceModuleIso D d f))))).symm

/-- 概要：同じ標準PD係数射に沿う実還元のH0は忠実平坦。
方針：raw PD 環の元の係数作用を標準環射の作用に同定し、一般 δ 完全化の定理へ渡す。
規約：係数作用の比較自体にはモニック性は不要。完全 prism 上の適用には任意正次数モニック族を使う。
使われ方：BS Rem 7.15（著者版 p.62）の最終完全 prism 候補への移送。 -/
theorem perfectPrismMonicPDSource_reductionH0_faithfullyFlat_arbitrary :
    letI := pdCompletionCommRing Raw p z
    Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj) := by
  let := pdCompletionCommRing Raw p z
  let : Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange q).obj (boundedAboveDerivedSingleFunctor.obj M)).obj) :=
    perfectPrismMonicRawPD_reductionH0_faithfullyFlat_arbitrary P hP f hf hdeg
  exact Module.FaithfullyFlat.of_linearEquiv Q
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange q).obj (boundedAboveDerivedSingleFunctor.obj M)).obj)
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange q).mapIso
        (boundedAboveDerivedSingleFunctor.mapIso
          (monicPrismaticPDSourceModuleIso D d f))))).toLinearEquiv.symm

/-- 概要：任意正次数モニック族の実PD環のδ完全化を逐次実完備化した具体的対象は離散。
方針：raw PD 環の元の係数作用を標準環射の作用に同定し、一般 δ 完全化の定理へ渡す。
規約：係数作用の比較自体にはモニック性は不要。完全 prism 上の適用には任意正次数モニック族を使う。
使われ方：BS Rem 7.15（著者版 p.62）の最終完全 prism 候補への移送。 -/
theorem perfectPrismMonicPDPerfectionCompletion_pure_arbitrary :
    letI := pdCompletionCommRing Raw p z
    let X := DeltaAlgebraPerfectionIteratedPDCompletion G j d
    X.obj.IsGE 0 ∧ X.obj.IsLE 0 := by
  let := pdCompletionCommRing Raw p z
  exact perfectPrismDeltaAlgebraCompletion_pure P G j hP
    (monicPrismaticPDSourceCoefficient_isDeltaHom D d f)
    (perfectPrismMonicPDSource_reduction_homology_isZero_arbitrary P hP f hf hdeg )
    (perfectPrismMonicPDSource_reductionH0_faithfullyFlat_arbitrary P hP f hf hdeg )

/-- 概要：同じ具体的δ完全化逐次対象の生成元冪商も離散でH0のp冪ねじれは有界。
方針：raw PD 環の元の係数作用を標準環射の作用に同定し、一般 δ 完全化の定理へ渡す。
規約：係数作用の比較自体にはモニック性は不要。完全 prism 上の適用には任意正次数モニック族を使う。
使われ方：BS Rem 7.15（著者版 p.62）の最終完全 prism 候補への移送。 -/
theorem perfectPrismMonicPDPerfectionPower_pure_bounded_torsion_arbitrary (n : ℕ) (hn : 0 < n) :
    letI := pdCompletionCommRing Raw p z
    let X := DeltaAlgebraPerfectionIteratedPDCompletion G j d
    let T := A ⧸ Ideal.span {d ^ n}
    let Z := (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X
    Z.obj.IsGE 0 ∧ Z.obj.IsLE 0 ∧
      ∃ N : ℕ, ∀ k : ℕ,
        ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{u} T) 0).obj Z.obj,
          (p : T) ^ k • x = 0 → (p : T) ^ N • x = 0 := by
  let := pdCompletionCommRing Raw p z
  exact perfectPrismDeltaAlgebraCompletionPower_pure_bounded_torsion P G j hP
    (monicPrismaticPDSourceCoefficient_isDeltaHom D d f)
    (perfectPrismMonicPDSource_reduction_homology_isZero_arbitrary P hP f hf hdeg )
    (perfectPrismMonicPDSource_reductionH0_faithfullyFlat_arbitrary P hP f hf hdeg ) n hn

local notation "C" => DeltaPerfection G
local notation "κ" => deltaAlgebraPerfectionCoefficient G j
local notation "t" => RingHom.comp (pdCompletionUnit C p (κ d)) κ

/-- 概要：任意正次数モニック族の raw PD 環を δ 完全化し再び実 PD 完備化した環は完全忠実平坦。
方針：元の標準係数射の実剰余の離散・忠実平坦性を、既存の一般 δ 代数の完全忠実平坦性へ渡す。
規約：元の (p,d) 係数作用を明示する。最終候補への環比較は別工程。
使われ方：BS Rem 7.15（著者版 p.62）の完成した完全 δ 環候補への平坦性の移送。 -/
theorem perfectPrismMonicPDPerfection_isCompletelyFaithfullyFlat_arbitrary :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p (κ d)
    IsCompletelyFaithfullyFlat I (ModuleCat.carrier (baseChangeScalarModule t)) := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p (κ d)
  exact perfectPrismDeltaAlgebraPD_isCompletelyFaithfullyFlat P G j hP
    (monicPrismaticPDSourceCoefficient_isDeltaHom D d f)
    (perfectPrismMonicPDSource_reduction_homology_isZero_arbitrary P hP f hf hdeg )
    (perfectPrismMonicPDSource_reductionH0_faithfullyFlat_arbitrary P hP f hf hdeg )

end Perfect
end SerrePositivity.BhattScholze.Andre
