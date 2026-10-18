module

public import SerrePositivity.EInfinity.BarrattEccles.Orbits
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.AlgebraicTopology.MooreComplex
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.CategoryTheory.Whiskering

/-!
# Barratt–Eccles の正規化複体

概要：Berger–Fresse §1.1 の E(n) を EΣₙ の自由 A 加群化の正規化 Moore 複体で定義する。
方針：単体加群から自然数次数の鎖複体を取り、q を −q に移して整数次数へ拡張する。
規約：Complex A はコチェイン複体で微分は +1、正次数は零である。
使われ方：Barratt–Eccles オペラッドの arity ごとの複体と右作用を与える。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：単体集合を自由な単体 A 加群へ送る（Berger–Fresse §1.1）。
方針：各次数で宇宙を持ち上げてから自由加群関手を適用する。
規約：入力は小さい単体集合、出力の加群の宇宙は A と同じ。
使われ方：EΣₙ の線形化を関手的に構成する。 -/
def linearization : SSet ⥤ SimplicialObject (ModuleCat A) :=
  (CategoryTheory.Functor.whiskeringRight _ _ _).obj
    (uliftFunctor.{u, 0} ⋙ ModuleCat.free A)

/-- 概要：小さい単体集合の正規化鎖を整数コチェイン複体へ送る（Berger–Fresse §1.1）。
方針：正規化 Moore 複体を次数 q ↦ −q の埋め込みで延長する。
規約：正次数を零で埋め、負次数に自然数次数の鎖を置く。
使われ方：単体集合上の構造射から Barratt–Eccles 複体上の射を作る。 -/
def normalizedFunctor : SSet ⥤ Complex A :=
  linearization A ⋙ AlgebraicTopology.normalizedMooreComplex (ModuleCat A) ⋙
    ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)

/-- 概要：Barratt–Eccles の arity n の正規化複体 E(n)（Berger–Fresse §1.1）。
方針：EΣₙ の単体集合に正規化鎖関手を適用する。
規約：群上の非正次数のコチェイン複体として実現する。
使われ方：E∞-dg オペラッドの arity 成分となる。 -/
def complex (n : ℕ) : Complex A := (normalizedFunctor A).obj (simplicial n)

/-- 概要：E(n) の Σₙ 右作用（Berger–Fresse §1.1）。
方針：単体集合上の右作用を正規化鎖関手で送る。
規約：右作用の順序は単体集合上の同時右乗法を継承する。
使われ方：E(n) の対称列と群加群構造を与える。 -/
def complexRightAction (n : ℕ) (σ : Equiv.Perm (Fin n)) : complex A n ⟶ complex A n :=
  (normalizedFunctor A).map (rightAction n σ)

/-- 概要：正規化複体上の単位置換の作用は恒等射である（Berger–Fresse §1.1）。
方針：正規化鎖関手の恒等射の保存を使う。
規約：任意の可換基礎環で成立する。
使われ方：Barratt–Eccles 対称列の単位作用の法則となる。 -/
@[simp] lemma complexRightAction_one (n : ℕ) : complexRightAction A n 1 = 𝟙 (complex A n) := by
  simp [complexRightAction, complex]

/-- 概要：正規化複体上の右作用は置換の積を保存する（Berger–Fresse §1.1）。
方針：単体集合の右作用の積の法則を正規化鎖関手で送る。
規約：右作用は σ、τ の順に適用する。
使われ方：Barratt–Eccles 対称列の作用の結合則となる。 -/
lemma complexRightAction_mul (n : ℕ) (σ τ : Equiv.Perm (Fin n)) :
    complexRightAction A n (σ * τ) = complexRightAction A n σ ≫ complexRightAction A n τ := by
  simp only [complexRightAction, rightAction_mul, CategoryTheory.Functor.map_comp]
  rfl

end SerrePositivity.EInfinity.BarrattEccles
