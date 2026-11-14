module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 完備多項式の pd Čech 模型

## 概要
頂点差の自由分冪 Čech 模型を項ごとに p 完備化する。

## 方針
主完備化の H⁰ 関手を用いる。

## 規約
各項の係数環は固定する。

## 使われ方
結晶比較と pd de Rham 比較。
-/

public noncomputable section

open CategoryTheory
universe u

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.DerivedCompletion

/-- 自由 pd 座標の多項式環の p 完備化。 -/
abbrev pdTerm (p : ℕ) (k : Type u) [CommRing k] (r n : ℕ) : CommRingCat.{u} :=
  principalCompletionRingCat p (CommRingCat.of (pdRaw k r n))

instance pdTermAlgebra (p : ℕ) (k : Type u) [CommRing k] (r n : ℕ) : Algebra k (pdTerm p k r n) :=
  ((principalCompletionRingCatUnit p (CommRingCat.of (pdRaw k r n))).hom.comp
    (algebraMap k (pdRaw k r n))).toAlgebra

/-- 頂点差の pd Čech 模型の項ごとの p 完備化。 -/
def pdModel (p : ℕ) (k : Type u) [CommRing k] (r : ℕ) :
    SerrePositivity.Cosimplicial.CosimplicialAlgebra k :=
  pdRawModel k r ⋙ principalCompletionUnder p (CommRingCat.of k)

end SerrePositivity.BhattScholze.Prismatic
