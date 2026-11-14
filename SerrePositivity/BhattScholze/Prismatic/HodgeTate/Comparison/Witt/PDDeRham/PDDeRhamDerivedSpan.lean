module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCech
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCompletedProjection
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDDeRhamColumnBounded
public import SerrePositivity.HomologicalAlgebra.BoundedAbove.Derived
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# 分冪 de Rham の二射影の有界導来圏での比較

## 概要
総複体と第 0 行を、二つの実際の射影を通して有界な第 0 列と比較する。

## 方針
既存の射影の擬同型を整数添字へ延長し、標準局所化で反転する。

## 規約
有界性はコホモロジーの有界性。第 0 行の項の有界性は必要としない。

## 使われ方
BS 著者版 Theorem 6.4 の完備底変換を第 0 列で計算する。
-/

public noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false
attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) (k : Type u) [CommRing k] (r : ℕ)

local notation "emb" => ComplexShape.embeddingUpNat
local notation "E" => ComplexShape.Embedding.extendFunctor emb (ModuleCat k) ⋙ DerivedCategory.Q
local notation "Total" => pdDeRhamTotal p k r
local notation "Row" => Functor.obj (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat k))
  (pdRow p k r 0)
local notation "Col" => pdDeRhamColumn p k r ⦋0⦌

/-- 整数添字の導来圏での第 0 行への実際の射影。 -/
def pdDeRhamDerivedRowIso : (E).obj Total ≅ (E).obj Row := by
  have := pdDeRhamRowZeroProjection_quasiIso p k r
  exact asIso (DerivedCategory.Q.map
    (HomologicalComplex.extendMap (pdDeRhamRowZeroProjection p k r) emb))

/-- 整数添字の導来圏での第 0 列への実際の射影。 -/
def pdDeRhamDerivedColumnIso : (E).obj Total ≅ (E).obj Col := by
  have := pdDeRhamCompletedColumnZeroProjection_quasiIso p k r
  exact asIso (DerivedCategory.Q.map
    (HomologicalComplex.extendMap (pdDeRhamColumnZeroProjection p k r) emb))

/-- 第 0 列から第 0 行への比較は、総複体の二射影で指定する。 -/
def pdDeRhamDerivedColumnRowIso : (E).obj Col ≅ (E).obj Row :=
  (pdDeRhamDerivedColumnIso p k r).symm ≪≫ pdDeRhamDerivedRowIso p k r

private theorem total_isLE : ((E).obj Total).IsLE (r : ℤ) := by
  have := pdDeRhamColumnZero_isStrictlyLE p k r
  let : ((E).obj Col).IsLE (r : ℤ) := by
    change (DerivedCategory.Q.obj ((Col).extend emb)).IsLE (r : ℤ)
    infer_instance
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (pdDeRhamDerivedColumnIso p k r).symm r

private theorem row_isLE : ((E).obj Row).IsLE (r : ℤ) := by
  have := total_isLE p k r
  exact DerivedCategory.TStructure.t.isLE_of_iso (pdDeRhamDerivedRowIso p k r) r

/-- 完備分冪総複体を上に有界な導来対象として読む。 -/
def pdDeRhamTotalDerived : DerivedCategory.Minus (ModuleCat.{u} k) :=
  ⟨(E).obj Total, ⟨r, total_isLE p k r⟩⟩

/-- 完備分冪第 0 行を上に有界な導来対象として読む。 -/
def pdDeRhamRowDerived : DerivedCategory.Minus (ModuleCat.{u} k) :=
  ⟨(E).obj Row, ⟨r, row_isLE p k r⟩⟩

/-- 第 0 列から総複体を経由した第 0 行への比較は、二射影の式を満たす。 -/
theorem pdDeRhamDerivedColumnRowIso_comm :
    (pdDeRhamDerivedColumnIso p k r).hom ≫
      (pdDeRhamDerivedColumnRowIso p k r).hom =
        (pdDeRhamDerivedRowIso p k r).hom := by
  simp [pdDeRhamDerivedColumnRowIso]

end SerrePositivity.BhattScholze.Prismatic
