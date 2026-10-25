module

public import SerrePositivity.BhattScholze.Andre.MonicPrismaticIteratedResidue
public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionSourceTensor
public import SerrePositivity.HomologicalAlgebra.DerivedTensorH0Algebra

/-!
# André E1・E2：モニック f/d 源と raw 包の実完備化比較

## 概要

一般モニック f/d 源の実 H⁰ を、同じ係数作用の raw 包およびその実完備化へ比較する。
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
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "P" => MvPolynomial σ A
local notation "L" => RelativeFreeDeltaRing (R := P) σ
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun t : σ => monicRelation (f t) t)
local notation "α" => deltaDivisionSourceMap (σ := σ) E (MvPolynomial.C d)
local notation "β" => deltaDivisionSourceEval E r
local notation "Mβ" => baseChangeScalarModule β
local notation "Mα" => baseChangeScalarModule α
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "X" => boundedAboveDerivedTensor.obj
  (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα)
local notation "C₀" => algebraMap A L

/-- 概要：raw包に、評価βを経由する元の実源L作用を明示した加群対象。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def MonicPrismaticSourceRawModule : ModuleCat.{u} L := by
  let := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
  let : Module L Raw := Algebra.toModule
  exact ModuleCat.of L Raw

/-- 概要：通常二因子テンソルとraw包は、元の実源L上で線形同型。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def monicPrismaticSourceOrdinaryTensorRawIso :
    (tensorLeft Mβ).obj Mα ≅ MonicPrismaticSourceRawModule D d f := by
  let := deltaDivisionSourceEvaluationAlgebra E r
  let := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
  let : Module L L := Algebra.toModule
  let := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
  let : Module L Raw := Algebra.toModule
  let e : P ⊗[L] L ≃ₐ[L] Raw :=
    AlgEquiv.ofRingEquiv (f := deltaDivisionSourceTensorEquiv E (MvPolynomial.C d) r) (by
      intro x
      change deltaDivisionSourceTensorEquiv E (MvPolynomial.C d) r
        (β x ⊗ₜ[L] 1) = (deltaAdjoinDivisionMap E (MvPolynomial.C d) r) (β x)
      rw [deltaDivisionSourceTensorEquiv_tmul, map_one, mul_one])
  exact e.toLinearEquiv.toModuleIso

set_option maxHeartbeats 800000 in
-- 二つの実係数作用と元の導来テンソル対象の型を同時に照合するため。
/-- 概要：元の実導来二因子源から、raw次数零対象への標準augmentation。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def monicPrismaticSourceRawAugmentation :
    X ⟶ boundedAboveDerivedSingleFunctor.obj (MonicPrismaticSourceRawModule D d f) := by
  let η : X ⟶ boundedAboveDerivedSingleFunctor.obj ((tensorLeft Mβ).obj Mα) :=
    ObjectProperty.homMk ((boundedAboveDerivedTensorModuleAugmentation (R := L) Mβ).app Mα)
  exact η ≫ boundedAboveDerivedSingleFunctor.map
    (monicPrismaticSourceOrdinaryTensorRawIso D d f).hom

set_option maxHeartbeats 800000 in
-- 二つの実係数作用と元の導来テンソル対象の型を同時に照合するため。
/-- 概要：元の実導来二因子源のH0と実源作用付きraw包の比較。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def monicPrismaticSourceRawH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat L) 0).obj (X).obj ≅
      MonicPrismaticSourceRawModule D d f :=
  (boundedAboveDerivedTensorModuleH0NatIso (R := L) Mβ).app Mα ≪≫
    monicPrismaticSourceOrdinaryTensorRawIso D d f

/-- 概要：raw標準augmentationはH0では同型である。高次の消滅はここでは主張しない。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem monicPrismaticSourceRawAugmentation_h0_isIso :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat L) 0).map
      (monicPrismaticSourceRawAugmentation D d f).hom) := by
  have := derivedTensorAugmentation_h0_isIso (R := L) Mβ Mα
  change IsIso ((DerivedCategory.homologyFunctor (ModuleCat L) 0).map
    (((boundedAboveDerivedTensorModuleAugmentation (R := L) Mβ).app Mα) ≫
      (DerivedCategory.singleFunctor (ModuleCat L) 0).map
        (monicPrismaticSourceOrdinaryTensorRawIso D d f).hom))
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

/-- 概要：元のAへ係数制限したraw次数零対象。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
abbrev MonicPrismaticSourceRawCoefficientObject :=
  (boundedAboveDerivedRestrictScalars C₀).obj
    (boundedAboveDerivedSingleFunctor.obj (MonicPrismaticSourceRawModule D d f))

set_option maxHeartbeats 800000 in
-- 元のテンソル対象の係数制限と実ホモロジーの型を同時に照合するため。
/-- 概要：元のAへ係数制限した実導来源のH0も、raw包の同じ係数制限と同型。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def monicPrismaticSourceRawCoefficientH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (MonicPrismaticSourceCoefficientObject D d f).obj ≅
      (ModuleCat.restrictScalars C₀).obj (MonicPrismaticSourceRawModule D d f) :=
  (derivedRestrictScalarsHomologyIso C₀ 0).app (X).obj ≪≫
    (ModuleCat.restrictScalars C₀).mapIso (monicPrismaticSourceRawH0Iso D d f)

/-- 概要：元のA上の実導来源からraw次数零対象への、同じ実係数制限による射。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def monicPrismaticSourceRawCoefficientAugmentation :
    MonicPrismaticSourceCoefficientObject D d f ⟶ MonicPrismaticSourceRawCoefficientObject D d f :=
  (boundedAboveDerivedRestrictScalars C₀).map (monicPrismaticSourceRawAugmentation D d f)

local notation "Cp" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)
local notation "Cd" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A d
local notation "Up" => DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)
local notation "Ud" => DerivedCompletion.boundedAboveDerivedCompletionUnit A d

/-- 概要：raw次数零対象へ元と同じp,d逐次実導来完備化を施した対象。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
abbrev MonicPrismaticSourceRawIteratedCompletion :=
  (Cd).obj ((Cp).obj (MonicPrismaticSourceRawCoefficientObject D d f))

/-- 概要：元の実逐次完備化源から、rawの同じ実逐次完備化への標準比較射。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def monicPrismaticSourceRawIteratedComparison :
    MonicPrismaticSourceIteratedPDCompletion D d f ⟶ MonicPrismaticSourceRawIteratedCompletion D d f :=
  (Cd).map ((Cp).map (monicPrismaticSourceRawCoefficientAugmentation D d f))

/-- 概要：完備化後の比較射は、元のp,d合成標準単位と可換。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem monicPrismaticSourceRawIteratedComparison_unit :
    ((Up).app (MonicPrismaticSourceCoefficientObject D d f) ≫
      (Ud).app ((Cp).obj (MonicPrismaticSourceCoefficientObject D d f))) ≫
        monicPrismaticSourceRawIteratedComparison D d f =
      monicPrismaticSourceRawCoefficientAugmentation D d f ≫
        ((Up).app (MonicPrismaticSourceRawCoefficientObject D d f) ≫
          (Ud).app ((Cp).obj (MonicPrismaticSourceRawCoefficientObject D d f))) := by
  let η := monicPrismaticSourceRawCoefficientAugmentation D d f
  have hp := (Up).naturality η
  have hd := (Ud).naturality ((Cp).map η)
  simp only [CategoryTheory.Functor.id_map] at hp hd
  dsimp only [monicPrismaticSourceRawIteratedComparison]
  rw [Category.assoc, ← hd, ← Category.assoc, ← hp, Category.assoc]

end SerrePositivity.BhattScholze.Andre
