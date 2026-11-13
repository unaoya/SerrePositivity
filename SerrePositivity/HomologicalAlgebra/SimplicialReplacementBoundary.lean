module

public import SerrePositivity.HomologicalAlgebra.SimplicialReplacement
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import all SerrePositivity.HomologicalAlgebra.SimplicialReplacement
import all Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
# 単体的置換の同じ射列の交代面境界

## 概要
各射列の因子上で、交代面微分を元の先頭への射と同じ面の包含の和へ分ける。

## 方針
交代面複体の微分の公式と、単体的置換の各因子上の公式を適用する。

## 規約
すべての面を同じ順序と整数符号で保持する。

## 使われ方
HA 1.2.4。strict coherent bar の面・先頭の射の列と全複体の境界の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite AlgebraicTopology
open scoped _root_.Simplicial
namespace SerrePositivity.HomologicalAlgebra
variable {J : Type} [SmallCategory J]
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{0} C]

/-- 各元の射列での交代面境界は、同じ先頭の射の後の同じ面の包含の和。 -/
@[reassoc]
theorem ι_simplicialReplacementBoundary (F : J ⥤ C) (n : ℕ)
    (s : ComposableArrows J (n + 1)) :
    Sigma.ι (replacementTerms F (op ⦋n + 1⦌)) s ≫
        (AlternatingFaceMapComplex.obj (simplicialReplacement F)).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        (F.map (s.map (homOfLE (Fin.zero_le ((SimplexCategory.δ i).toOrderHom 0)))) ≫
          Sigma.ι (replacementTerms F (op ⦋n⦌)) ((nerve J).map (SimplexCategory.δ i).op s)) := by
  rw [AlternatingFaceMapComplex.obj_d_eq, comp_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [comp_zsmul]
  congr 1
  exact ι_replacementMap F (SimplexCategory.δ i).op s

end SerrePositivity.HomologicalAlgebra
