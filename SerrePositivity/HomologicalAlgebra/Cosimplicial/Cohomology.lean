module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# 余単体的可換環の加法的コホモロジー

## 概要
余単体的可換環から非正規化余鎖複体を作り、射のコホモロジーへの作用を定める。

## 方針
加法可換群への忘却と、Mathlib の交代余面複体・ホモロジー関手を使う。

## 規約
余鎖微分は余面の交代和。

## 使われ方
余単体的な cup 積と Bockstein、mod p の比較射。
-/

@[expose] public section
noncomputable section

universe u

open CategoryTheory
open scoped Simplicial

namespace SerrePositivity.Cosimplicial

variable (X : CosimplicialObject CommRingCat.{u})

local notation "U" => (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)

/-- 概要：余単体的環の交代余面微分。
方針：加法可換群への忘却後、Mathlib の交代余面微分を取る。
規約：最初の余面の符号は正。
使われ方：cup 積と Bockstein の代表元計算。 -/
def cochainDifferential (n : ℕ) : X.obj ⦋n⦌ →+ X.obj ⦋n + 1⦌ :=
  (AlgebraicTopology.AlternatingCofaceMapComplex.objD (X ⋙ U) n).hom

/-- 概要：余単体的可換環の非正規化複体のコホモロジー。
方針：加法可換群の交代余面複体にホモロジー関手を適用する。
規約：余鎖の次数 n で取る。
使われ方：cup 積と結晶比較。 -/
abbrev cohomology (n : ℕ) : Type u :=
  ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u}).obj (X ⋙ U)).homology n

/-- 概要：コホモロジーと交代余面複体のホモロジーとの加法的な同一視。
方針：定義どおりの同一視。
規約：台加法群で計算する。
使われ方：加群上で作る Bockstein を加法群のコホモロジーへ移す。 -/
def cohomologyEquivHomology (n : ℕ) :
    cohomology X n ≃+ ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u}).obj
      (X ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).homology n :=
  AddEquiv.refl _

variable (Y : CosimplicialObject CommRingCat.{u})

/-- 概要：余単体的環の射がコホモロジーに誘導する準同型。
方針：忘却した自然変換に余鎖複体とホモロジーの関手を適用する。
規約：各次数の加法準同型。
使われ方：比較射のコホモロジー同型。 -/
def cohomologyMap (f : X ⟶ Y) (n : ℕ) : cohomology X n →+ cohomology Y n :=
  (HomologicalComplex.homologyMap ((AlgebraicTopology.alternatingCofaceMapComplex _).map
    (Functor.whiskerRight f U)) n).hom

/-- 概要：余単体的環の射が全次数でコホモロジー同型であるという述語。
方針：誘導される加法準同型の全単射性。
規約：非正規化複体で判定する。
使われ方：mod p の結晶比較。 -/
def IsCohomologyIso {X Y : CosimplicialObject CommRingCat.{u}} (f : X ⟶ Y) : Prop :=
  ∀ n, Function.Bijective (cohomologyMap X Y f n)

/-- コホモロジー同型から得られる各次数の加法群同型。 -/
def IsCohomologyIso.addEquiv {X Y : CosimplicialObject CommRingCat.{u}} {f : X ⟶ Y}
    (h : IsCohomologyIso f) (n : ℕ) : cohomology X n ≃+ cohomology Y n :=
  AddEquiv.ofBijective (cohomologyMap X Y f n) (h n)

/-- 余単体的環の同型はコホモロジー同型を誘導する。 -/
theorem isCohomologyIso_of_isIso {X Y : CosimplicialObject CommRingCat.{u}} (f : X ⟶ Y)
    [IsIso f] : IsCohomologyIso f := by
  intro n
  let F := (Functor.whiskeringRight SimplexCategory CommRingCat AddCommGrpCat).obj U ⋙
    AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) n
  exact ConcreteCategory.bijective_of_isIso (F.map f)

end SerrePositivity.Cosimplicial
