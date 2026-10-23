module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeTrianglePathFaces
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeRestrictedHomPath
public import SerrePositivity.InfinityCategories.F1.EquivalenceTriangleFaceEvaluation

/-!
概要：元の比較三角形の第二面の path と、その元の二つの分類図式への端点評価。
方針：同じ三角形の共有頂点を、既存の最初の面と長辺で評価する。
規約：元の比較三角形の第二面そのもの。
使われ方：元の第二面の同じ Hom 上で二段の輸送を回収する。
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

/-- 元の比較三角形の同じ第二面の可逆 path の全族。 -/
def cocartesianBaseChangeSecondHomPath :
    CocartesianFibrationInfinity (nerve C) ⟶
      equivalencePath (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) :=
  cocartesianBaseChangeEquivalenceTriangle l k ≫ equivalenceTriangleFace _ 0

/-- 同じ第二面の零端点は、元の最初の面の同じ一端点。 -/
lemma cocartesianBaseChangeSecondHomPath_zero :
    cocartesianBaseChangeSecondHomPath l k ≫ equivalencePathEndpoint _ 0 =
      cocartesianBaseChangeRestrictedHomPath l k ≫ equivalencePathEndpoint _ 1 := by
  have h : equivalenceTriangleFace
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) 0 ≫
        equivalencePathEndpoint _ 0 = equivalenceTriangleFace
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) 2 ≫
        equivalencePathEndpoint _ 1 := by
    rw [equivalenceTriangleFace_endpoint, equivalenceTriangleFace_endpoint]
    exact congrArg (equivalenceTriangleEvaluation _) (show
      (0 : Fin 3).succAbove (0 : Fin 2) = (2 : Fin 3).succAbove (1 : Fin 2) by decide)
  rw [cocartesianBaseChangeSecondHomPath, Category.assoc, h, ← Category.assoc,
    cocartesianBaseChangeEquivalenceTriangle_first]
  rfl

/-- 同じ第二面の一端点は、元の直接の比較の同じ一端点。 -/
lemma cocartesianBaseChangeSecondHomPath_one :
    cocartesianBaseChangeSecondHomPath l k ≫ equivalencePathEndpoint _ 1 =
      cocartesianBaseChangeHomPath (l ⋙ k) ≫ equivalencePathEndpoint _ 1 := by
  have h : equivalenceTriangleFace
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) 0 ≫
        equivalencePathEndpoint _ 1 = equivalenceTriangleFace
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) 1 ≫
        equivalencePathEndpoint _ 1 := by
    rw [equivalenceTriangleFace_endpoint, equivalenceTriangleFace_endpoint]
    exact congrArg (equivalenceTriangleEvaluation _) (show
      (0 : Fin 3).succAbove (1 : Fin 2) = (1 : Fin 3).succAbove (1 : Fin 2) by decide)
  rw [cocartesianBaseChangeSecondHomPath, Category.assoc, h, ← Category.assoc,
    cocartesianBaseChangeEquivalenceTriangle_long]

/-- 同じ第二面の零頂点は、元の底変換対象の分類図式の底制限。 -/
lemma cocartesianBaseChangeSecondHomPath_zero_vertex
    (p : CocartesianFibrationCategory (nerve C)) :
    (cocartesianBaseChangeSecondHomPath l k ≫ equivalencePathEndpoint _ 0).app _
      (coherentNerveVertex p) = functorVertex
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l) ≫ cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p).val.hom) := by
  rw [cocartesianBaseChangeSecondHomPath_zero]
  exact cocartesianBaseChangeRestrictedHomPath_one_vertex l k p

/-- 同じ第二面の一頂点は、元の直接の底変換対象の分類図式。 -/
lemma cocartesianBaseChangeSecondHomPath_one_vertex
    (p : CocartesianFibrationCategory (nerve C)) :
    (cocartesianBaseChangeSecondHomPath l k ≫ equivalencePathEndpoint _ 1).app _
      (coherentNerveVertex p) = functorVertex (cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj p).val.hom) := by
  rw [cocartesianBaseChangeSecondHomPath_one]
  exact cocartesianBaseChangeHomPath_one_vertex (l ⋙ k) p

end SerrePositivity.InfinityCategories
