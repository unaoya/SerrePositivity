module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeHomPath
public import SerrePositivity.InfinityCategories.F1.Cocartesian.StraighteningVertices

/-!
概要：元の比較 path の両端を、制限した分類図式と底変換後の分類図式へ正規化する。
方針：同じ path の両端の厳密な等式と、元の分類写像の頂点公式を使う。
規約：図式全体の端点を固定し、各値の独立な同値で置き換えない。
使われ方：同じ比較 path の Hom の両端評価。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C)

/-- 同じ path の零端点は、元の分類図式全体の同じ底の制限。 -/
lemma cocartesianBaseChangeHomPath_zero_vertex
    (p : CocartesianFibrationCategory (nerve C)) :
    (cocartesianBaseChangeHomPath k ≫ equivalencePathEndpoint _ 0).app
      (Opposite.op ⦋0⦌) (coherentNerveVertex p) =
      functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
        cocartesianStrictTransportCoherentDiagram p.val.hom) := by
  rw [cocartesianBaseChangeHomPath_zero]
  change ((pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k))).app CatInfinity).app _
    ((cocartesianStraighteningCoherentMap C).app _ (coherentNerveVertex p)) = _
  have hp : (cocartesianStraighteningCoherentMap C).app (Opposite.op ⦋0⦌)
      (coherentNerveVertex p) = functorVertex (cocartesianStrictTransportCoherentDiagram p.val.hom) :=
    cocartesianStraighteningCoherentMap_vertex p.val.hom
  rw [hp]
  rfl

/-- 同じ path の一端点は、元の底変換対象の同じ分類図式全体。 -/
lemma cocartesianBaseChangeHomPath_one_vertex
    (p : CocartesianFibrationCategory (nerve C)) :
    (cocartesianBaseChangeHomPath k ≫ equivalencePathEndpoint _ 1).app
      (Opposite.op ⦋0⦌) (coherentNerveVertex p) =
      functorVertex (cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p).val.hom) := by
  rw [cocartesianBaseChangeHomPath_one]
  change (cocartesianStraighteningCoherentMap D).app _
    ((cocartesianFibrationInfinityBaseChange (nerveMap k)).app _ (coherentNerveVertex p)) = _
  rw [cocartesianFibrationInfinityBaseChange_vertex]
  exact cocartesianStraighteningCoherentMap_vertex
    ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p).val.hom

end SerrePositivity.InfinityCategories
