module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeSecondTriangleHomFirst
public import SerrePositivity.InfinityCategories.F1.IntervalHomFamilyProjection

/-!
概要：同じ分解三角形の Hom の長辺は、元の大域比較三角形の第二面の Hom。
方針：同じ長辺の族の等式を、元の全端点固定 Hom に移す。
規約：元の比較三角形の第二面そのものを回収する。
使われ方：同じ第二面の元の Hom 輸送の分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 同じ分解三角形の Hom を、元の比較三角形の同じ第二面の Hom へ射影する。 -/
def cocartesianBaseChangeSecondTriangleHomLong :
    cocartesianBaseChangeSecondTriangleHomSpace l k p q ⟶ intervalMappingSpace
      ((cocartesianBaseChangeEquivalenceTriangle l k ≫ equivalenceTriangleFace _ 0).app _
        (coherentNerveVertex p))
      ((cocartesianBaseChangeEquivalenceTriangle l k ≫ equivalenceTriangleFace _ 0).app _
        (coherentNerveVertex q)) :=
  intervalHomFamilyProjection (cocartesianBaseChangeSecondEquivalenceTriangle l k)
    (equivalenceTriangleFace _ 1)
    (cocartesianBaseChangeEquivalenceTriangle l k ≫ equivalenceTriangleFace _ 0)
    (cocartesianBaseChangeSecondEquivalenceTriangle_long l k)
    (coherentNerveVertex p) (coherentNerveVertex q)

/-- 同じ長辺への射影は、元の比較三角形の同じ第二面の Hom との同値。 -/
lemma cocartesianBaseChangeSecondTriangleHomLong_isQCatEquivalence :
    IsQCatEquivalence (cocartesianBaseChangeSecondTriangleHomLong l k p q) :=
  intervalHomFamilyProjection_isQCatEquivalence _ _ _ _ _ _
    (equivalenceTriangleFace_isQCatEquivalence _ 1).isFullyFaithful

/-- 同じ長辺への射影後の作用は、元の比較三角形の同じ第二面の Hom 作用そのもの。 -/
lemma cocartesianBaseChangeSecondTriangleHomComparison_long :
    cocartesianBaseChangeSecondTriangleHomComparison l k p q ≫
        cocartesianBaseChangeSecondTriangleHomLong l k p q =
      coherentHomIntervalComparison p q ≫ intervalMappingPost
        (cocartesianBaseChangeEquivalenceTriangle l k ≫ equivalenceTriangleFace _ 0)
        (coherentNerveVertex p) (coherentNerveVertex q) := by
  have h := intervalHomFamilyProjection_factor
    (cocartesianBaseChangeSecondEquivalenceTriangle l k) (equivalenceTriangleFace _ 1)
    (cocartesianBaseChangeEquivalenceTriangle l k ≫ equivalenceTriangleFace _ 0)
    (cocartesianBaseChangeSecondEquivalenceTriangle_long l k)
    (coherentNerveVertex p) (coherentNerveVertex q)
  simpa only [cocartesianBaseChangeSecondTriangleHomComparison,
    cocartesianBaseChangeSecondTriangleHomLong, Category.assoc] using
      congrArg (fun f ↦ coherentHomIntervalComparison p q ≫ f) h

end SerrePositivity.InfinityCategories
