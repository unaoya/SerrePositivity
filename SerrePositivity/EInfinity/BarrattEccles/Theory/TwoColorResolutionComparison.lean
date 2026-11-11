module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorTensorAugmentation
public import SerrePositivity.EInfinity.BarrattEccles.Theory.ResolutionAugmentationComparison

/-!
# 二色の実際の解像度の比較

## 概要
HA 3.2.4.7 の二色比較に使う、二つの実際の射影解像度の比較定理。

## 方針
二色部分群への制限で得た自明表現を同定し、指定増大を保つ射に解像度の比較を適用する。

## 規約
順射は引数として指定された比較射のまま保つ。増大の可換性を仮定に明示する。

## 使われ方
実際の係数射の構成後、その等変な鎖ホモトピー逆を供給する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A]

/-- 始域の制限した自明表現と、終域の自明表現の指定同型。 -/
def twoColorTrivialIso (m n : ℕ) :
    twoColorTrivialRepresentation A m n ≅
      Rep.trivial A (TwoColorGroup.{u} m n) (𝟙_ (ModuleCat A)) := Iso.refl _

/-- 共通の自明表現を値とする、指定された始域の解像度。 -/
def twoColorSourceResolutionCommon (m n : ℕ) :
    ProjectiveResolution (Rep.trivial A (TwoColorGroup.{u} m n) (𝟙_ (ModuleCat A))) :=
  twoColorSourceResolution A m n

/-- 指定増大を保つ実際の係数射は、等変な鎖ホモトピー同値の順射になる。 -/
def twoColorResolutionHomotopyEquiv (m n : ℕ)
    (f : (twoColorSourceResolutionCommon A m n).complex ⟶
      (twoColorTargetResolution A m n).complex)
    (hf : f ≫ (twoColorTargetResolution A m n).π =
      (twoColorSourceResolutionCommon A m n).π) :
    HomotopyEquiv (twoColorSourceResolutionCommon A m n).complex
      (twoColorTargetResolution A m n).complex :=
  resolutionHomotopyEquivOfAugmentation (P := twoColorSourceResolutionCommon A m n)
    (Q := twoColorTargetResolution A m n) f hf

/-- 比較定理は指定された順射を置き換えない。 -/
@[simp]
lemma twoColorResolutionHomotopyEquiv_hom (m n : ℕ)
    (f : (twoColorSourceResolutionCommon A m n).complex ⟶
      (twoColorTargetResolution A m n).complex)
    (hf : f ≫ (twoColorTargetResolution A m n).π =
      (twoColorSourceResolutionCommon A m n).π) :
    (twoColorResolutionHomotopyEquiv A m n f hf).hom = f := rfl

end SerrePositivity.EInfinity.BarrattEccles
