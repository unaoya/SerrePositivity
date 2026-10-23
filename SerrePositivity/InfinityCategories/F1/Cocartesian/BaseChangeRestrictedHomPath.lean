module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeHomPathVertices
public import SerrePositivity.InfinityCategories.Core.EquivalencePathMap

/-!
概要：元の底変換比較 path を、底の同じ関手で制限した全高次の族。
方針：元の可逆 path の族に、図式の同じ前合成を作用させる。
規約：元の path と元の二つの分類図式を保持する。
使われ方：既存の元の Hom 輸送の底の制限に関する自然性。
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

/-- 元の比較 path の全高次の族を、同じ底の前合成で制限する。 -/
def cocartesianBaseChangeRestrictedHomPath :
    CocartesianFibrationInfinity (nerve C) ⟶
      equivalencePath (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) :=
  cocartesianBaseChangeHomPath k ≫ equivalencePathMap
    ((pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l))).app CatInfinity.{u})

/-- 同じ制限した比較 path の両端は、元の両端を同じ底で制限したもの。 -/
lemma cocartesianBaseChangeRestrictedHomPath_endpoint (i : Fin 2) :
    cocartesianBaseChangeRestrictedHomPath l k ≫ equivalencePathEndpoint _ i =
      (cocartesianBaseChangeHomPath k ≫ equivalencePathEndpoint _ i) ≫
        (pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l))).app CatInfinity.{u} := by
  rw [cocartesianBaseChangeRestrictedHomPath, Category.assoc,
    equivalencePathMap_endpoint, Category.assoc]

/-- 同じ制限した比較 path の零端点は、元の分類図式を同じ二つの底の射で制限したもの。 -/
lemma cocartesianBaseChangeRestrictedHomPath_zero_vertex
    (p : CocartesianFibrationCategory (nerve C)) :
    (cocartesianBaseChangeRestrictedHomPath l k ≫ equivalencePathEndpoint _ 0).app
      (Opposite.op ⦋0⦌) (coherentNerveVertex p) =
      functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l) ≫
        (SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
          cocartesianStrictTransportCoherentDiagram p.val.hom) := by
  rw [cocartesianBaseChangeRestrictedHomPath_endpoint]
  change ((pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l))).app CatInfinity).app _
    ((cocartesianBaseChangeHomPath k ≫ equivalencePathEndpoint _ 0).app _
      (coherentNerveVertex p)) = _
  rw [cocartesianBaseChangeHomPath_zero_vertex]
  exact functorVertex_precomposition _ _

/-- 同じ制限した比較 path の一端点は、元の底変換対象の分類図式を同じ底で制限したもの。 -/
lemma cocartesianBaseChangeRestrictedHomPath_one_vertex
    (p : CocartesianFibrationCategory (nerve C)) :
    (cocartesianBaseChangeRestrictedHomPath l k ≫ equivalencePathEndpoint _ 1).app
      (Opposite.op ⦋0⦌) (coherentNerveVertex p) =
      functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l) ≫
        cocartesianStrictTransportCoherentDiagram
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p).val.hom) := by
  rw [cocartesianBaseChangeRestrictedHomPath_endpoint]
  change ((pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l))).app CatInfinity).app _
    ((cocartesianBaseChangeHomPath k ≫ equivalencePathEndpoint _ 1).app _
      (coherentNerveVertex p)) = _
  rw [cocartesianBaseChangeHomPath_one_vertex]
  exact functorVertex_precomposition _ _

end SerrePositivity.InfinityCategories
