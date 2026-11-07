-- 将来の置き場所：共有層（HomologicalAlgebra/Cosimplicial/CupProduct など。調整役と相談）。BS 固有ではない。
-- 設計書：formalization-plans/bhatt-scholze/a1-design.md G-A1-1。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.HomologicalAlgebra.Cosimplicial.CupCohomology
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Ring.Basic

/-!
# 余単体的可換環の非正規化複体の cup 積（Alexander–Whitney）

## 概要
余単体的可換環 X^•（SimplexCategory ⥤ CommRingCat）の非正規化余鎖複体（交代余面複体、Mathlib の `alternatingCofaceMapComplex`）に、
Alexander–Whitney の cup 積 x ∪ y := (前面 [m] → [m+n])^*(x) · (後面 [n] → [m+n])^*(y) で次数付き環の構造を入れ、Leibniz 則から dg 環に
なること、コホモロジー環 H^*(X^•) が次数付き可換であることを示す。

## 方針
前面・後面の射を `SimplexCategory.mkHom` で与える。結合律・単位律は余単体的恒等式から、Leibniz 則は余面写像の交代和の計算から。
次数付き可換性はコホモロジーで（鎖のレベルでは成り立たない。cup₁ 積のホモトピー）。

## 規約
X^n の元は CommRingCat の台の元。複体の次数 n に X^n。係数環 k 上の余単体的 k 代数なら k 線形。
E∞ 構造（Barratt–Eccles）はここでは扱わない（G-A1-11）。

## 使われ方
A1 の HT 比較の写像（Constr 4.9）：H^*(Ō_{R/A}) の模型 H^*(Tot(C^•/d)) の環構造。Lemma 5.4 の計算。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace SerrePositivity.Cosimplicial

variable (X : CosimplicialObject CommRingCat.{u})

/-- 概要：コホモロジー環は次数付き可換：a ∪ b = (−1)^{mn} b ∪ a。
方針：鎖のレベルの cup₁ ホモトピー（Steenrod）、または余単体的可換環の cup 積が E∞ の H^* であること。
規約：鎖のレベルでは主張しない。
使われ方：Constr 4.9 の H^*(Ō) の次数付き可換性（原典の「generalities on cohomology of commutative ring objects」）。 -/
theorem cohomologyCup_comm {m n : ℕ} (a : cohomology X m) (b : cohomology X n) :
    cast (by rw [Nat.add_comm]) (cohomologyCup X a b) = (-1 : ℤ) ^ (m * n) • cohomologyCup X b a := by
  sorry -- cup₁ 積のホモトピー

end SerrePositivity.Cosimplicial
