module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarUnshiftedBoundary
public import SerrePositivity.HomologicalAlgebra.SimplicialReplacementBoundary
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalValues
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalColumns
import all SerrePositivity.HomologicalAlgebra.SimplicialReplacement

/-!
# シフト前の bar 列の全ての面の符号付き和

## 概要
同じ列の微分を、元の面ごとの先頭の射と同じ包含の有限和へ分解する。

## 方針
標準列との合成を加法群準同型にまとめ、元の交代面境界の和を移す。

## 規約
すべての面の順序・整数符号と、同じ射列の値を保つ。

## 使われ方
HA 1.2.4。既存 theta の一次列を合成した値との比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open HomologicalComplex CochainComplex HomComplex SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open SerrePositivity.HomologicalAlgebra
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]

local instance smallStrictBarBoundarySum_hasCoproducts : HasCoproducts.{0} (Complex A) := fun _ =>
  HomologicalComplex.instHasColimitsOfShape

/-- 元の一つの面の先頭の射を作用させ、同じ面の因子の標準列へ送る項。 -/
def smallStrictBarBoundaryTerm (F : J ⥤ ModuleCategory A PUnit.{1}) (n : ℕ)
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n + 1⦌) (i : Fin (n + 2)) :
    Cochain ((smallStrictBarCoefficientDiagram A F).obj (s.down.obj 0))
      ((smallStrictBarTotalTarget A F).obj (op PUnit.unit)) (-((n + 1 : ℕ) : ℤ) + 1) :=
  (Cochain.ofHom
    ((smallStrictBarCoefficientDiagram A F).map
        (s.down.map (homOfLE (Fin.zero_le ((SimplexCategory.δ i).toOrderHom 0)))) ≫
      Sigma.ι (replacementTerms (smallStrictBarCoefficientDiagram A F) (op ⦋n⦌))
        ((nerve J).map (SimplexCategory.δ i).op s.down))).comp
    (standardRowCochain A (simplicialReplacement (smallStrictBarCoefficientDiagram A F)) n)
    (by omega)

/-- 同じシフト前の列の微分を、元のすべての面の同じ符号付き和として計算する。 -/
theorem smallStrictBarUnshiftedColumn_boundary_sum (F : J ⥤ ModuleCategory A PUnit.{1}) (n : ℕ)
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n + 1⦌) :
    δ (-((n + 1 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ) + 1)
        (smallStrictBarUnshiftedColumn A F ⟨n + 1, s⟩) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • smallStrictBarBoundaryTerm A F n s i := by
  let X := smallStrictBarCoefficientDiagram A F
  let L : (X.obj (s.down.obj 0) ⟶ (simplicialReplacement X).obj (op ⦋n⦌)) →+
      Cochain (X.obj (s.down.obj 0)) ((smallStrictBarTotalTarget A F).obj (op PUnit.unit))
        (-((n + 1 : ℕ) : ℤ) + 1) :=
    { toFun f := (Cochain.ofHom f).comp (standardRowCochain A (simplicialReplacement X) n) (by omega)
      map_zero' := by simp
      map_add' f g := by simp }
  rw [smallStrictBarUnshiftedColumn_boundary]
  change L (Sigma.ι (replacementTerms X (op ⦋n + 1⦌)) s.down ≫
    (AlternatingFaceMapComplex.obj (simplicialReplacement X)).d (n + 1) n) = _
  rw [ι_simplicialReplacementBoundary, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
