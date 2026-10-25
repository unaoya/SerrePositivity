module

public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.PowerRootSourceComplete
public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionSourceTensor
public import SerrePositivity.HomologicalAlgebra.DerivedTensorH0Algebra

/-!
# André E1・E2：モニック f/d 源と raw 包の実完備化比較

## 概要

元の無限根モニック源の実 H⁰ を、同じ係数作用の raw 包およびその実完備化へ比較する。
BS Rem 7.15（著者版 p.62）の raw PD 環との比較の準備。

## 方針

一般 δ 除算の通常テンソル表示、標準 augmentation、実係数制限と完備化の既存比較を再利用する。
原典の Prop 7.11 を使う経路とは異なる、具体的な元の係数作用を保つ計算。

## 規約

この H⁰ 比較にはモニック性・正次数・有限性は不要。高次ホモロジー消滅は別の証明を使う。

## 使われ方

実完備化源の離散性と組み合わせ、元の係数射の完全忠実平坦性を raw PD 環へ移す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
/-- 概要：通常テンソルの指定同型を標準導来 augmentation へ合成する。
方針：実テンソルの標準 H⁰ 比較を使う。
規約：モニック性・平坦性・有限性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の元の raw 実完備化との比較。 -/
def unconditionalTensorRawAugmentation {S : Type u} [CommRing S]
    (M N K : ModuleCat.{u} S) (e : (tensorLeft M).obj N ≅ K) :
    boundedAboveDerivedTensor.obj
      (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N) ⟶
        boundedAboveDerivedSingleFunctor.obj K := by
  let η : boundedAboveDerivedTensor.obj
      (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N) ⟶
        boundedAboveDerivedSingleFunctor.obj ((tensorLeft M).obj N) :=
    ObjectProperty.homMk ((boundedAboveDerivedTensorModuleAugmentation M).app N)
  exact η ≫ boundedAboveDerivedSingleFunctor.map e.hom

/-- 概要：指定した標準 augmentation は H⁰ で同型を誘導する。
方針：実テンソルの標準 H⁰ 比較を使う。
規約：モニック性・平坦性・有限性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の元の raw 実完備化との比較。 -/
theorem unconditionalTensorRawAugmentation_h0_isIso {S : Type u} [CommRing S]
    (M N K : ModuleCat.{u} S) (e : (tensorLeft M).obj N ≅ K) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat S) 0).map
      (unconditionalTensorRawAugmentation M N K e).hom) := by
  have := derivedTensorAugmentation_h0_isIso M N
  change IsIso ((DerivedCategory.homologyFunctor (ModuleCat S) 0).map
    (((boundedAboveDerivedTensorModuleAugmentation M).app N) ≫
      (DerivedCategory.singleFunctor (ModuleCat S) 0).map e.hom))
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

/-- 概要：二因子の実導来テンソルの H⁰ 比較は元の係数制限と両立する。
方針：実テンソルの標準 H⁰ 比較を使う。
規約：モニック性・平坦性・有限性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の元の raw 実完備化との比較。 -/
def unconditionalRestrictedTensorRawH0Iso {S T : Type u} [CommRing S] [CommRing T]
    (k : T →+* S) (M N K : ModuleCat.{u} S) (e : (tensorLeft M).obj N ≅ K) :
    (DerivedCategory.homologyFunctor (ModuleCat T) 0).obj
      ((boundedAboveDerivedRestrictScalars k).obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N))).obj ≅
      (ModuleCat.restrictScalars k).obj K :=
  (derivedRestrictScalarsHomologyIso k 0).app _ ≪≫
    (ModuleCat.restrictScalars k).mapIso
      ((boundedAboveDerivedTensorModuleH0NatIso M).app N ≪≫ e)

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hpNat" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "D" => W.deltaStructure
local notation "d" => W.generator
local notation "dP" => algebraMap A (PowerRootPolynomial A p hpNat) d
local notation "P" => PowerRootPolynomial A p hpNat
local notation "L" => PowerRootUnaryFreeDeltaRing A p hpNat
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "r" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "α" =>
  deltaDivisionSourceMap (σ := PUnit) E dP
local notation "β" => deltaDivisionSourceEval E r
local notation "Mβ" => baseChangeScalarModule β
local notation "Mα" => baseChangeScalarModule α
local notation "Raw" => DeltaAdjoinDivision E dP r
local notation "X" => boundedAboveDerivedTensor.obj
  (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα)
local notation "C₀" => algebraMap A L

/-- 概要：raw包に、評価βを経由する元の実源L作用を明示した加群対象。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def PowerRootPrismMonicSourceRawModule_of_unconditional : ModuleCat.{u} L := by
  let := deltaDivisionSourceRawAlgebra E dP r
  let : Module L Raw := Algebra.toModule
  exact ModuleCat.of L Raw

/-- 概要：通常二因子テンソルとraw包は、元の実源L上で線形同型。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def powerRootPrismMonicSourceOrdinaryTensorRawIso_of_unconditional :
    (tensorLeft Mβ).obj Mα ≅ PowerRootPrismMonicSourceRawModule_of_unconditional W hW f := by
  let := deltaDivisionSourceEvaluationAlgebra E r
  let := deltaDivisionSourceTargetAlgebra (σ := PUnit.{u + 1}) E dP
  let : Module L L := Algebra.toModule
  let := deltaDivisionSourceRawAlgebra E dP r
  let : Module L Raw := Algebra.toModule
  let e : P ⊗[L] L ≃ₐ[L] Raw :=
    AlgEquiv.ofRingEquiv (f := deltaDivisionSourceTensorEquiv E dP r) (by
      intro x
      change deltaDivisionSourceTensorEquiv E dP r
        (β x ⊗ₜ[L] 1) = (deltaAdjoinDivisionMap E dP r) (β x)
      rw [deltaDivisionSourceTensorEquiv_tmul, map_one, mul_one])
  exact e.toLinearEquiv.toModuleIso

set_option maxHeartbeats 100000 in
-- 二つの実係数作用と元の導来テンソル対象の型を同時に照合するため。
set_option backward.isDefEq.respectTransparency true in
/-- 概要：元の実導来二因子源から、raw次数零対象への標準augmentation。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def powerRootPrismMonicSourceRawAugmentation_of_unconditional :
    X ⟶ boundedAboveDerivedSingleFunctor.obj (PowerRootPrismMonicSourceRawModule_of_unconditional W hW f) := by
  with_reducible exact (unconditionalTensorRawAugmentation (S := L) Mβ Mα
    (PowerRootPrismMonicSourceRawModule_of_unconditional W hW f)
    (powerRootPrismMonicSourceOrdinaryTensorRawIso_of_unconditional W hW f))

set_option maxHeartbeats 100000 in
-- 二つの実係数作用と元の導来テンソル対象の型を同時に照合するため。
/-- 概要：元の実導来二因子源のH0と実源作用付きraw包の比較。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def powerRootPrismMonicSourceRawH0Iso_of_unconditional :
    (DerivedCategory.homologyFunctor (ModuleCat L) 0).obj (X).obj ≅
      PowerRootPrismMonicSourceRawModule_of_unconditional W hW f :=
  (boundedAboveDerivedTensorModuleH0NatIso (R := L) Mβ).app Mα ≪≫
    powerRootPrismMonicSourceOrdinaryTensorRawIso_of_unconditional W hW f

set_option backward.isDefEq.respectTransparency true in
/-- 概要：raw標準augmentationはH0では同型である。高次の消滅はここでは主張しない。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem powerRootPrismMonicSourceRawAugmentation_h0_isIso_of_unconditional :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat L) 0).map
      (powerRootPrismMonicSourceRawAugmentation_of_unconditional W hW f).hom) := by
  unfold powerRootPrismMonicSourceRawAugmentation_of_unconditional
  with_reducible exact (unconditionalTensorRawAugmentation_h0_isIso (S := L) Mβ Mα
    (PowerRootPrismMonicSourceRawModule_of_unconditional W hW f)
    (powerRootPrismMonicSourceOrdinaryTensorRawIso_of_unconditional W hW f))

/-- 概要：元のAへ係数制限したraw次数零対象。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
abbrev PowerRootPrismMonicSourceRawCoefficientObject_of_unconditional :=
  (boundedAboveDerivedRestrictScalars C₀).obj
    (boundedAboveDerivedSingleFunctor.obj (PowerRootPrismMonicSourceRawModule_of_unconditional W hW f))

set_option maxHeartbeats 100000 in
-- 元のテンソル対象の係数制限と実ホモロジーの型を同時に照合するため。
/-- 概要：元のAへ係数制限した実導来源のH0も、raw包の同じ係数制限と同型。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def powerRootPrismMonicSourceRawCoefficientH0Iso_of_unconditional :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f).obj ≅
      (ModuleCat.restrictScalars C₀).obj (PowerRootPrismMonicSourceRawModule_of_unconditional W hW f) :=
  unconditionalRestrictedTensorRawH0Iso C₀ Mβ Mα
    (PowerRootPrismMonicSourceRawModule_of_unconditional W hW f)
    (powerRootPrismMonicSourceOrdinaryTensorRawIso_of_unconditional W hW f)

/-- 概要：元のA上の実導来源からraw次数零対象への、同じ実係数制限による射。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def powerRootPrismMonicSourceRawCoefficientAugmentation_of_unconditional :
    PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f ⟶ PowerRootPrismMonicSourceRawCoefficientObject_of_unconditional W hW f :=
  (boundedAboveDerivedRestrictScalars C₀).map (powerRootPrismMonicSourceRawAugmentation_of_unconditional W hW f)

local notation "Cp" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)
local notation "Cd" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A d
local notation "Up" => DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)
local notation "Ud" => DerivedCompletion.boundedAboveDerivedCompletionUnit A d

/-- 概要：raw次数零対象へ元と同じp,d逐次実導来完備化を施した対象。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
abbrev PowerRootPrismMonicSourceRawIteratedCompletion_of_unconditional :=
  (Cd).obj ((Cp).obj (PowerRootPrismMonicSourceRawCoefficientObject_of_unconditional W hW f))

/-- 概要：元の実逐次完備化源から、rawの同じ実逐次完備化への標準比較射。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def powerRootPrismMonicSourceRawIteratedComparison_of_unconditional :
    PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional W hW f ⟶ PowerRootPrismMonicSourceRawIteratedCompletion_of_unconditional W hW f :=
  (Cd).map ((Cp).map (powerRootPrismMonicSourceRawCoefficientAugmentation_of_unconditional W hW f))

/-- 概要：完備化後の比較射は、元のp,d合成標準単位と可換。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem powerRootPrismMonicSourceRawIteratedComparison_unit_of_unconditional :
    ((Up).app (PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f) ≫
      (Ud).app ((Cp).obj (PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f))) ≫
        powerRootPrismMonicSourceRawIteratedComparison_of_unconditional W hW f =
      powerRootPrismMonicSourceRawCoefficientAugmentation_of_unconditional W hW f ≫
        ((Up).app (PowerRootPrismMonicSourceRawCoefficientObject_of_unconditional W hW f) ≫
          (Ud).app ((Cp).obj (PowerRootPrismMonicSourceRawCoefficientObject_of_unconditional W hW f))) := by
  let η := powerRootPrismMonicSourceRawCoefficientAugmentation_of_unconditional W hW f
  have hp := (Up).naturality η
  have hd := (Ud).naturality ((Cp).map η)
  simp only [CategoryTheory.Functor.id_map] at hp hd
  dsimp only [powerRootPrismMonicSourceRawIteratedComparison_of_unconditional]
  rw [Category.assoc, ← hd, ← Category.assoc, ← hp, Category.assoc]

end SerrePositivity.BhattScholze.Andre
