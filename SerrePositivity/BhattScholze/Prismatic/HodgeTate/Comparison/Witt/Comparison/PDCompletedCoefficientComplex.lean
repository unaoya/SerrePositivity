module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDTermPointwiseNaturality
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.MapComplex

/-!
# 小さい分冪交代余面複体の完備係数比較

## 概要
各項の完備係数拡大を小さい分冪交代余面複体に適用すると、係数変更後の複体と同型になる。

## 方針
加法的関手と交代余面複体の交換同型に、実際の余単体的な係数比較を合成する。

## 規約
各項の H⁰ 完備係数拡大による古典的な複体。複体全体の導来テンソルとの同定は述べない。
各項が導来底変換を計算する条件は、別の完全平坦性の補題で確認する。

## 使われ方
BS 著者版 Theorem 6.4、Witt 係数の二比較のうち小さい分冪側。
-/

public noncomputable section
open CategoryTheory AlgebraicTopology
open SerrePositivity.DerivedCompletion
universe u
namespace SerrePositivity.BhattScholze.Prismatic
variable (p : ℕ) (k l : Type u) [CommRing k] [CommRing l] [Algebra k l] (r : ℕ)

/-- 小さい分冪交代余面複体へ各項の完備係数拡大を適用した標準の比較同型。 -/
def pdCompletedCoefficientComplexIso :
    ((pCompletedScalarExtensionFunctor p (algebraMap k l)).mapHomologicalComplex _).obj
      ((alternatingCofaceMapComplex (ModuleCat.{u} k)).obj
        (SerrePositivity.Cosimplicial.toModules k (pdCechRings p k r) (pdCechBase p k r))) ≅
    (alternatingCofaceMapComplex (ModuleCat.{u} l)).obj
      (SerrePositivity.Cosimplicial.toModules l (pdCechRings p l r) (pdCechBase p l r)) :=
  (SerrePositivity.Cosimplicial.alternatingCofaceMapComplexCompMapHomologicalComplexIso
      (pCompletedScalarExtensionFunctor p (algebraMap k l))).app
        (SerrePositivity.Cosimplicial.toModules k (pdCechRings p k r) (pdCechBase p k r)) ≪≫
    pdCechPointwiseCoefficientCochainIso p k l r

end SerrePositivity.BhattScholze.Prismatic
