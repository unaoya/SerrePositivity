module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorCoefficientAugmentation

/-!
# 二色の指定係数比較の等変な鎖ホモトピー逆

## 概要
HA 3.2.4.7 の実際の二色係数比較は、任意の可換環上で等変な鎖ホモトピー同値となる。

## 方針
指定された増大の零次成分を照合し、二つの実際の射影解像度の比較定理を適用する。

## 規約
順射は `twoColorCoefficientChainMap` を保持し、増大の可換性を証明して供給する。

## 使われ方
自由代数と実際のセル対の余積からテンソルへの比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A]

/-- 実際の係数鎖写像は、二つの解像度の指定された増大を保つ。 -/
lemma twoColorCoefficientChainMap_augmentation (m n : ℕ) :
    twoColorCoefficientChainMap A m n ≫ (twoColorTargetResolution A m n).π =
      (twoColorSourceResolutionCommon A m n).π := by
  apply HomologicalComplex.to_single_hom_ext
  apply (forget₂ (Rep.{u} A (TwoColorGroup.{u} m n)) (ModuleCat.{u} A)).map_injective
  apply ModuleCat.hom_ext
  ext x
  change (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
      ((twoColorTensorAugmentation A m n).f 0 ((twoColorCoefficientComparison A m n).f 0 x)) =
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
      ((complexAugmentation A (m + n)).f 0 x)
  exact congrArg (fun y => (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom y)
    (congrArg (fun f => f.f (0 : ℤ) x) (twoColorCoefficientComparison_augmentation A m n))

/-- 実際の二色係数比較の、任意の可換基礎環上の等変な鎖ホモトピー同値。 -/
def twoColorCoefficientHomotopyEquiv (m n : ℕ) :
    HomotopyEquiv (twoColorSourceResolutionCommon A m n).complex
      (twoColorTargetResolution A m n).complex :=
  twoColorResolutionHomotopyEquiv A m n (twoColorCoefficientChainMap A m n)
    (twoColorCoefficientChainMap_augmentation A m n)

/-- 等変なホモトピー同値の順射は、元の指定された係数比較である。 -/
@[simp]
lemma twoColorCoefficientHomotopyEquiv_hom (m n : ℕ) :
    (twoColorCoefficientHomotopyEquiv A m n).hom = twoColorCoefficientChainMap A m n := rfl

/-- 指定された二色係数比較は、表現の圏で擬同型である。 -/
lemma twoColorCoefficientChainMap_quasiIso (m n : ℕ) :
    QuasiIso (twoColorCoefficientChainMap A m n) :=
  HomotopyEquiv.quasiIso_hom (twoColorCoefficientHomotopyEquiv A m n)

end SerrePositivity.EInfinity.BarrattEccles
