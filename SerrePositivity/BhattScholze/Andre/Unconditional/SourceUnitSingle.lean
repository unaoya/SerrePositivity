module

public import SerrePositivity.BhattScholze.Andre.Unconditional.SourceUnitPurity
public import SerrePositivity.HomologicalAlgebra.ScalarConeModuleQuotient

/-!
# 単元分母の実源と元の評価加群

## 概要
BS Rem 7.15（著者版 p.62）の分母可逆部分の実源を、元の評価加群へ比較する。

## 方針
右因子の実源自己同型を逆にして自由一階加群へ移し、標準 augmentation を合成する。

## 規約
元の評価による作用を保持し、通常の single との具体的な同型を作る。

## 使われ方
局所化先の p 正則性から、元の実源の局所化後の p 錐純性を供給する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard

/-- 概要：右因子が自由一階で標準 augmentation が同型なら、実テンソルは左因子の single。
方針：右因子の同型とテンソルの右単位同型を合成する。
規約：標準 augmentation の同型性を明示する一般補題。
使われ方：BS Rem 7.15（著者版 p.62）の具体的な元の作用の比較。 -/
def unconditionalTensorSingleIso_of_unit_right
    {R : Type u} [CommRing R] (M N : ModuleCat.{u} R) (eN : N ≅ ModuleCat.of R R)
    (h : IsIso ((boundedAboveDerivedTensorModuleAugmentation M).app N)) :
    (boundedAboveDerivedTensor.obj
      (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N)).obj ≅
        (DerivedCategory.singleFunctor (ModuleCat R) 0).obj M := by
  have := h
  let e := (tensorLeft M).mapIso eN ≪≫ (ρ_ M)
  exact asIso ((boundedAboveDerivedTensorModuleAugmentation M).app N) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat R) 0).mapIso e

variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (hd : IsUnit d) (a : σ → A)
local notation "L" => RelativeFreeDeltaRing (R := A) σ
local notation "Mα" => baseChangeScalarModule (deltaDivisionSourceMap (σ := σ) D d)
local notation "Mβ" => baseChangeScalarModule (deltaDivisionSourceEval D a)
local notation "X" => boundedAboveDerivedTensor.obj
  (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα)

/-- 概要：単元分母で作用する右因子は、元の係数環の自由一階加群と線形同型。
方針：実源自己同型の逆を台写像にする。
規約：元の自己射作用を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の実源の H⁰ の同定。 -/
def unconditionalSourceUnitScalarModuleEquiv : Mα ≃ₗ[L] L := by
  let e := RingEquiv.ofBijective (deltaDivisionSourceMap (σ := σ) D d)
    (unconditionalDeltaDivisionSourceMap_bijective_of_isUnit D d hd)
  exact
    { e.symm.toAddEquiv with
      map_smul' := by
        intro r x
        change L at x
        change e.symm (deltaDivisionSourceMap D d r * x) = r * e.symm x
        rw [map_mul]
        congr 1
        exact e.symm_apply_apply r }

set_option backward.isDefEq.respectTransparency true in
/-- 概要：単元分母の元の実二因子源は、元の評価加群の single と同型。
方針：標準 augmentation と右因子の自由一階比較を合成する。
規約：元の β による係数作用を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の局所化先の p 錐の計算。 -/
def unconditionalSourceUnitSingleIso :
    (X).obj ≅ (DerivedCategory.singleFunctor (ModuleCat L) 0).obj Mβ := by
  let eM : Mα ≅ ModuleCat.of L L := (unconditionalSourceUnitScalarModuleEquiv D d hd).toModuleIso
  with_reducible exact (unconditionalTensorSingleIso_of_unit_right Mβ Mα eM
    (unconditionalSourceUnit_augmentation_isIso D d hd a))

include hd in
/-- 概要：係数環の p が正則なら、単元分母の元の実源の p 錐は非零次数で消える。
方針：元の評価加群の p 正則性と、実スカラー錐の通常商比較を使う。
規約：分子の正則性・モニック性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の局所化側の先行 p 還元。 -/
theorem unconditionalSourceUnit_primeCone_homology_isZero
    (hp : IsSMulRegular A (p : A)) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat L) i).obj
      ((derivedScalarConeFunctor L (p : L)).obj (X).obj)) := by
  have hM : IsSMulRegular Mβ (p : L) := by
    intro x y hxy
    change A at x y
    change deltaDivisionSourceEval D a (p : L) * x =
      deltaDivisionSourceEval D a (p : L) * y at hxy
    rw [map_natCast] at hxy
    exact hp hxy
  let e := (derivedScalarConeFunctor L (p : L)).mapIso
    (unconditionalSourceUnitSingleIso D d hd a)
  have eQ := derivedScalarConeModuleQuotientIso (p : L) Mβ hM 1
  rw [pow_one] at eQ
  exact (derivedSingleHomology_isZero (modulePowerReduction (p : L) Mβ 1) i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat L) i).mapIso (e ≪≫ eQ))

end SerrePositivity.BhattScholze.Andre
