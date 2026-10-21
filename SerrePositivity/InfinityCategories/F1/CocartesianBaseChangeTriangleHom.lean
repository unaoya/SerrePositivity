module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeTrianglePathFaces

/-!
概要：同じ可逆比較三角形の Hom は、元の直接の比較 span へ射影する。
方針：元の相対 Hom の区間族を同じ三角形へ後合成し、長辺を制限する。
規約：長辺の射影は既存の元の比較作用そのものを回収する。
使われ方：元の Hom 比較 span の合成と局所比較の降下。
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

/-- 元の二つの fibration での同じ可逆三角形の間の全区間 Hom。 -/
def cocartesianBaseChangeTriangleHomSpace : SSet.{u + 1} :=
  intervalMappingSpace
    ((cocartesianBaseChangeEquivalenceTriangle l k).app _ (coherentNerveVertex p))
    ((cocartesianBaseChangeEquivalenceTriangle l k).app _ (coherentNerveVertex q))

/-- 元の全相対 Hom を、同じ比較三角形の Hom へ写す。 -/
def cocartesianBaseChangeTriangleHomComparison :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom p q) ⟶
      cocartesianBaseChangeTriangleHomSpace l k p q :=
  coherentHomComparison p q ≫
    pinchedHomToIntervalMappingSpace (coherentNerveVertex p) (coherentNerveVertex q) ≫
      intervalMappingPost (cocartesianBaseChangeEquivalenceTriangle l k)
        (coherentNerveVertex p) (coherentNerveVertex q)

/-- 同じ三角形への比較の展開は、元の全相対 Hom の同じ prism の後合成。 -/
lemma cocartesianBaseChangeTriangleHomComparison_uncurry :
    intervalMappingUncurry (cocartesianBaseChangeTriangleHomComparison l k p q) =
      rightMappingSpacePrism _ ≫ pinchedHomUncurry (coherentHomComparison p q) ≫
        cocartesianBaseChangeEquivalenceTriangle l k := by
  rw [cocartesianBaseChangeTriangleHomComparison, ← Category.assoc,
    intervalMappingPost_uncurry, pinchedHomToIntervalMappingSpace_uncurry]
  rfl

/-- 同じ三角形の Hom の長辺を、既存の直接の比較 path の Hom へ射影する。 -/
def cocartesianBaseChangeTriangleHomLong :
    cocartesianBaseChangeTriangleHomSpace l k p q ⟶
      cocartesianBaseChangeHomComparisonSpace (l ⋙ k) p q :=
  intervalMappingPostOfEq
    (X := equivalenceTriangle
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))))
    (Y := equivalencePath
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))))
    (equivalenceTriangleFace _ 1)
    ((cocartesianBaseChangeEquivalenceTriangle l k).app _ (coherentNerveVertex p))
    ((cocartesianBaseChangeEquivalenceTriangle l k).app _ (coherentNerveVertex q))
    (x' := (cocartesianBaseChangeHomPath (l ⋙ k)).app _ (coherentNerveVertex p))
    (y' := (cocartesianBaseChangeHomPath (l ⋙ k)).app _ (coherentNerveVertex q))
    (congrArg (fun f : CocartesianFibrationInfinity (nerve C) ⟶ equivalencePath
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) ↦
        f.app (Opposite.op ⦋0⦌) (coherentNerveVertex p))
      (cocartesianBaseChangeEquivalenceTriangle_long l k))
    (congrArg (fun f : CocartesianFibrationInfinity (nerve C) ⟶ equivalencePath
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) ↦
        f.app (Opposite.op ⦋0⦌) (coherentNerveVertex q))
      (cocartesianBaseChangeEquivalenceTriangle_long l k))

/-- 長辺への射影後の同じ作用は、既存の元の直接の Hom 比較そのもの。 -/
lemma cocartesianBaseChangeTriangleHomComparison_long :
    cocartesianBaseChangeTriangleHomComparison l k p q ≫
        cocartesianBaseChangeTriangleHomLong l k p q =
      cocartesianBaseChangeHomComparison (l ⋙ k) p q := by
  apply intervalMappingUncurry_injective
  rw [cocartesianBaseChangeTriangleHomLong, intervalMappingPostOfEq_uncurry,
    cocartesianBaseChangeTriangleHomComparison_uncurry, cocartesianBaseChangeHomComparison_uncurry,
    Category.assoc, Category.assoc, cocartesianBaseChangeEquivalenceTriangle_long]

end SerrePositivity.InfinityCategories
