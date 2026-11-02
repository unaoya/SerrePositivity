-- 将来の置き場所：共有層（HomologicalAlgebra/Cosimplicial/CupProduct など。調整役と相談）。BS 固有ではない。
-- 設計書：formalization-plans/bhatt-scholze/a1-design.md G-A1-1。基準コミット 972bb7f53。ビルドしない。
module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
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

/-- 概要：前面 [m] → [m+n]、i ↦ i。
方針：`SimplexCategory.mkHom` と単調写像。
規約：—
使われ方：cup 積の第一因子の引き戻し。 -/
def frontFace (m n : ℕ) : (⦋m⦌ : SimplexCategory) ⟶ ⦋m + n⦌ :=
  SimplexCategory.mkHom ⟨fun i => ⟨i, by omega⟩, fun _ _ h => h⟩

/-- 概要：後面 [n] → [m+n]、i ↦ m + i。
方針：同上。
規約：—
使われ方：cup 積の第二因子の引き戻し。 -/
def backFace (m n : ℕ) : (⦋n⦌ : SimplexCategory) ⟶ ⦋m + n⦌ :=
  SimplexCategory.mkHom ⟨fun i => ⟨m + i, by omega⟩, fun _ _ h => by simpa using h⟩

variable (X : CosimplicialObject CommRingCat.{u})

/-- 概要：cup 積 X^m × X^n → X^{m+n}、x ∪ y := (frontFace)^*(x) · (backFace)^*(y)。
方針：Alexander–Whitney。
規約：双線形。
使われ方：非正規化複体の dg 環構造。 -/
def cup {m n : ℕ} (x : X.obj ⦋m⦌) (y : X.obj ⦋n⦌) : X.obj ⦋m + n⦌ :=
  X.map (frontFace m n) x * X.map (backFace m n) y

/-- 概要：cup 積の結合律（鎖のレベルで成り立つ）。
方針：前面・後面の合成の余単体的恒等式と環の結合律。
規約：次数の和の結合は `Nat.add_assoc` で移す。
使われ方：dg 環。 -/
theorem cup_assoc {l m n : ℕ} (x : X.obj ⦋l⦌) (y : X.obj ⦋m⦌) (z : X.obj ⦋n⦌) :
    cast (by rw [Nat.add_assoc]) (cup X (cup X x y) z) = cup X x (cup X y z) := by
  sorry -- frontFace (l+m) n ∘ frontFace l m = frontFace l (m+n) など

/-- 概要：単位元 1 ∈ X^0 は cup 積の単位。
方針：面写像は環射なので 1 を保つ。
規約：—
使われ方：dg 環。 -/
theorem one_cup {n : ℕ} (y : X.obj ⦋n⦌) : cast (by simp) (cup X (1 : X.obj ⦋0⦌) y) = y := by
  sorry

/-- 概要：交代余面複体の微分 d_n : X^n → X^{n+1}（Σ (−1)^i δ^i）。
方針：Mathlib の `CosimplicialObject.alternatingCofaceMapComplex` の微分（加群として読む）。
規約：ModuleCat ℤ、または係数環 k の上。
使われ方：Leibniz 則の主張。
要確認：CommRingCat の余単体的対象を加群の余単体的対象へ送る忘却関手の名前。 -/
def cochainDifferential (n : ℕ) : X.obj ⦋n⦌ →+ X.obj ⦋n + 1⦌ :=
  sorry -- Σ_{i} (−1)^i X.map (SimplexCategory.δ i)

/-- 概要：Leibniz 則 d(x ∪ y) = dx ∪ y + (−1)^m x ∪ dy。
方針：δ^i と前面・後面の可換関係：i ≤ m では δ^i ∘ frontFace = frontFace ∘ δ^i、backFace との合成は i による。中間の項が相殺する。
規約：符号は非正規化複体の標準のもの。
使われ方：非正規化複体が dg 環であること。 -/
theorem cochainDifferential_cup {m n : ℕ} (x : X.obj ⦋m⦌) (y : X.obj ⦋n⦌) :
    cast (by omega) (cochainDifferential X (m + n) (cup X x y)) =
      cast (by omega) (cup X (cochainDifferential X m x) y) +
        (-1 : ℤ) ^ m • cup X x (cochainDifferential X n y) := by
  sorry -- Alexander–Whitney の標準計算

/-- 概要：コホモロジー H^n(X^•) := H^n の交代余面複体。
方針：Mathlib の `HomologicalComplex.homology`。
規約：ModuleCat の対象。
使われ方：コホモロジー環。 -/
def cohomology (n : ℕ) : Type u :=
  sorry -- (alternatingCofaceMapComplex.obj (X ⋙ forget₂ CommRingCat (ModuleCat ℤ))).homology n

/-- 概要：cup 積はコホモロジーに降りる（Leibniz 則から、余輪体 × 余輪体 ⊆ 余輪体、余境界 × 余輪体 ⊆ 余境界）。
方針：`cochainDifferential_cup`。
規約：—
使われ方：コホモロジー環。 -/
def cohomologyCup {m n : ℕ} : cohomology X m → cohomology X n → cohomology X (m + n) :=
  sorry

/-- 概要：コホモロジー環は次数付き可換：a ∪ b = (−1)^{mn} b ∪ a。
方針：鎖のレベルの cup₁ ホモトピー（Steenrod）、または余単体的可換環の cup 積が E∞ の H^* であること。
規約：鎖のレベルでは主張しない。
使われ方：Constr 4.9 の H^*(Ō) の次数付き可換性（原典の「generalities on cohomology of commutative ring objects」）。 -/
theorem cohomologyCup_comm {m n : ℕ} (a : cohomology X m) (b : cohomology X n) :
    cast (by rw [Nat.add_comm]) (cohomologyCup X a b) = (-1 : ℤ) ^ (m * n) • cohomologyCup X b a := by
  sorry -- cup₁ 積のホモトピー

/-- 概要：余単体的環の射 X → Y は cup 積を保ち、コホモロジー環の射を誘導する。
方針：面写像と環射の可換性。
規約：—
使われ方：模型の取り替え（大小の Čech–Alexander 模型、底変換）で環構造が移ること。 -/
theorem cohomologyCup_map (Y : CosimplicialObject CommRingCat.{u}) (f : X ⟶ Y) : True := by
  trivial -- 要確認：cohomology の関手性の型を決めてから述べる

end SerrePositivity.Cosimplicial
