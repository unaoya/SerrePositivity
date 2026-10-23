module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeTriangleHomEquivalence

/-!
概要：元の比較三角形の Hom の最初の面は、既存の元の Hom 比較の底制限。
方針：同じ面の厳密な path の等式を、端点固定の全 Hom へ移す。
規約：元の比較作用と元の底制限作用を変更しない。
使われ方：元の Hom 比較 span の合成とセル制限の整合性。
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
  (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 同じ元の比較三角形の Hom を、元の最初の比較 path の底制限の Hom へ送る。 -/
def cocartesianBaseChangeTriangleHomFirst :
    cocartesianBaseChangeTriangleHomSpace l k p q ⟶ intervalMappingSpace
      ((cocartesianBaseChangeHomPath k ≫ equivalencePathMap
        ((pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l))).app CatInfinity.{u})).app _
          (coherentNerveVertex p))
      ((cocartesianBaseChangeHomPath k ≫ equivalencePathMap
        ((pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l))).app CatInfinity.{u})).app _
          (coherentNerveVertex q)) :=
  intervalMappingPostOfEq
    (X := equivalenceTriangle
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))))
    (Y := equivalencePath
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))))
    (equivalenceTriangleFace _ 2)
    ((cocartesianBaseChangeEquivalenceTriangle l k).app _ (coherentNerveVertex p))
    ((cocartesianBaseChangeEquivalenceTriangle l k).app _ (coherentNerveVertex q))
    (congrArg (fun f : CocartesianFibrationInfinity (nerve C) ⟶ equivalencePath
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) ↦
        f.app (Opposite.op ⦋0⦌) (coherentNerveVertex p))
      (cocartesianBaseChangeEquivalenceTriangle_first l k))
    (congrArg (fun f : CocartesianFibrationInfinity (nerve C) ⟶ equivalencePath
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) ↦
        f.app (Opposite.op ⦋0⦌) (coherentNerveVertex q))
      (cocartesianBaseChangeEquivalenceTriangle_first l k))

/-- 最初の面への同じ射影は同値。 -/
lemma cocartesianBaseChangeTriangleHomFirst_isQCatEquivalence :
    IsQCatEquivalence (cocartesianBaseChangeTriangleHomFirst l k p q) := by
  unfold cocartesianBaseChangeTriangleHomFirst
  exact (equivalenceTriangleFace_isQCatEquivalence _ 2).isFullyFaithful
    |>.intervalMappingPostOfEq_isQCatEquivalence _ _ _ _

/-- 元の三角形の同じ Hom 作用の最初の面は、既存の元の比較作用の底制限そのもの。 -/
lemma cocartesianBaseChangeTriangleHomComparison_first :
    cocartesianBaseChangeTriangleHomComparison l k p q ≫
        cocartesianBaseChangeTriangleHomFirst l k p q =
      cocartesianBaseChangeHomComparison k p q ≫ intervalMappingPost
        (equivalencePathMap
          (X := CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve D)))
          (Y := CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A)))
          ((pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l))).app CatInfinity.{u}))
        ((cocartesianBaseChangeHomPath k).app _ (coherentNerveVertex p))
        ((cocartesianBaseChangeHomPath k).app _ (coherentNerveVertex q)) := by
  apply intervalMappingUncurry_injective
  rw [cocartesianBaseChangeTriangleHomFirst, intervalMappingPostOfEq_uncurry,
    cocartesianBaseChangeTriangleHomComparison_uncurry, intervalMappingPost_uncurry,
    cocartesianBaseChangeHomComparison_uncurry, Category.assoc, Category.assoc,
    cocartesianBaseChangeEquivalenceTriangle_first, Category.assoc]
  simp only [Category.assoc]

end SerrePositivity.InfinityCategories
