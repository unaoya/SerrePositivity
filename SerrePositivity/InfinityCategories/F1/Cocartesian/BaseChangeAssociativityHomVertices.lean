module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeAssociativityHomPath
public import SerrePositivity.InfinityCategories.F1.Cocartesian.StraighteningVertices

/-!
概要：元の結合比較 path の両端を、同じ二回・直接の底変換の分類図式へ正規化する。
方針：既存の元の両端の族の等式と、分類主写像の頂点公式を使う。
規約：元の全 fibration の図式全体を保持する。
使われ方：元の結合比較の同じ Hom span の両端評価。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C)

/-- 同じ結合比較 path の零端点は、元の二回の底変換対象の分類図式そのもの。 -/
lemma cocartesianBaseChangeAssociativityHomPath_zero_vertex
    (p : CocartesianFibrationCategory (nerve C)) :
    (cocartesianBaseChangeAssociativityHomPath l k ≫ equivalencePathEndpoint _ 0).app
      (Opposite.op ⦋0⦌) (coherentNerveVertex p) =
      functorVertex (cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)).val.hom) := by
  rw [cocartesianBaseChangeAssociativityHomPath_zero]
  change (cocartesianStraighteningCoherentMap A).app _
    ((cocartesianFibrationInfinityBaseChange (nerveMap l)).app _
      ((cocartesianFibrationInfinityBaseChange (nerveMap k)).app _ (coherentNerveVertex p))) = _
  rw [cocartesianFibrationInfinityBaseChange_vertex, cocartesianFibrationInfinityBaseChange_vertex]
  exact cocartesianStraighteningCoherentMap_vertex _

/-- 同じ結合比較 path の一端点は、元の直接の底変換対象の分類図式そのもの。 -/
lemma cocartesianBaseChangeAssociativityHomPath_one_vertex
    (p : CocartesianFibrationCategory (nerve C)) :
    (cocartesianBaseChangeAssociativityHomPath l k ≫ equivalencePathEndpoint _ 1).app
      (Opposite.op ⦋0⦌) (coherentNerveVertex p) =
      functorVertex (cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj p).val.hom) := by
  rw [cocartesianBaseChangeAssociativityHomPath_one]
  change (cocartesianStraighteningCoherentMap A).app _
    ((cocartesianFibrationInfinityBaseChange (nerveMap (l ⋙ k))).app _ (coherentNerveVertex p)) = _
  rw [cocartesianFibrationInfinityBaseChange_vertex]
  exact cocartesianStraighteningCoherentMap_vertex _

end SerrePositivity.InfinityCategories
