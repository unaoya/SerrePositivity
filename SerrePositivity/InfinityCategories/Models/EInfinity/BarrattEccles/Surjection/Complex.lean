module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Chains
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import Mathlib.Algebra.Homology.Embedding.Extend

/-!
模型。文献の定義との比較は後で
# 全射語の非有界整数コチェイン複体

概要：Berger–Fresse §1.2 の χ(n) を本リポジトリの整数コチェイン規約で実現する。
方針：実際の非負鎖複体を q ↦ −q で零延長する。
規約：鎖次数 q は整数コチェイン次数 −q、正次数は零対象。
使われ方：χ の対称 dg オペラッドと TR オペラッド射の対象成分。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.CategoryTheory

variable (A : Type u) [CommRing A]

/-- 概要：χ(n) の整数コチェイン複体（BF §1.2.1–3）。
方針：符号付き削除微分の鎖複体を次数 q ↦ −q で延長する。
規約：非正次数のみに台を持つ非有界複体として扱う。
使われ方：Operad の各 arity の対象。 -/
def complex (n : ℕ) : _root_.SerrePositivity.DifferentialGraded.Complex A :=
  (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.normalizedChains A n)

/-- 概要：χ(n) の次数 −q は元の全射語加群（BF §1.2.1）。
方針：次数延長の標準同型を取る。
規約：基底と削除符号を変更しない。
使われ方：成分の部分合成を整数複体の射へ組み立てる。 -/
def complexXIso (n q : ℕ) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).X (-(q : ℤ)) ≅ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n q :=
  HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat rfl

/-- 概要：χ(n) の正次数の成分は零対象（BF §1.2.1）。
方針：正整数が q ↦ −q の像でないことを使う。
規約：arity は零を含む。
使われ方：合成・単位・TR の整数成分の正次数の場合を閉じる。 -/
lemma complex_isZero_positive (n : ℕ) (k : ℤ) (hk : 0 < k) :
    Limits.IsZero ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).X k) := by
  apply HomologicalComplex.isZero_extend_X
  intro q
  change -(q : ℤ) ≠ k
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
