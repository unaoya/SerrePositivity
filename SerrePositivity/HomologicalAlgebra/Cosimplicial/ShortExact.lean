module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
# 余単体的加群の短完全列

## 概要
項ごとの短完全列から交代余面複体の短完全列とコホモロジーの連結写像を作る。

## 方針
短完全性を各次数で確かめて、Mathlib のホモロジー長完全列を適用する。

## 規約
非正規化余鎖複体を用い、連結写像の符号は Mathlib に従う。

## 使われ方
正則元による商の Bockstein。
-/

@[expose] public section
noncomputable section

universe u

open CategoryTheory
open scoped Simplicial

namespace SerrePositivity.Cosimplicial

variable {k : Type u} [CommRing k]

/-- 概要：余単体的加群の項ごとの短完全列。
方針：合成が零の自然変換二本と各項の短完全性を持たせる。
規約：全項で共通の係数環を用いる。
使われ方：余単体的 Bockstein の入力。 -/
structure CosimplicialShortExact (M' M M'' : CosimplicialObject (ModuleCat.{u} k)) where
  ι : M' ⟶ M
  π : M ⟶ M''
  zero : ι ≫ π = 0
  exact : ∀ n : SimplexCategory,
    (ShortComplex.mk (ι.app n) (π.app n) (congrArg (fun f => f.app n) zero)).ShortExact

namespace CosimplicialShortExact

variable {M' M M'' : CosimplicialObject (ModuleCat.{u} k)}
variable (s : CosimplicialShortExact M' M M'')

local notation "F" => AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat k)

/-- 概要：余単体的短完全列の交代余面複体は短完全。
方針：各次数で元の短完全列に戻す。
規約：次数 n の項は単体 [n] で評価する。
使われ方：コホモロジーの連結写像。 -/
theorem cochainShortExact :
    (ShortComplex.mk ((F).map s.ι) ((F).map s.π) (by
      rw [← (F).map_comp, s.zero]
      ext n x
      rfl)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact s.exact ⦋n⦌

/-- 概要：交代余面複体の短完全列から得るコホモロジーの連結写像。
方針：Mathlib のホモロジー長完全列を使う。
規約：余鎖の次数を一つ上げる。
使われ方：正則元による商の Bockstein。 -/
def bockstein (i : ℕ) : ((F).obj M'').homology i ⟶ ((F).obj M').homology (i + 1) :=
  s.cochainShortExact.δ i (i + 1) rfl

end CosimplicialShortExact

end SerrePositivity.Cosimplicial
