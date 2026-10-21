module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeSecondTriangleHomFirst
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeAssociativityHomComparison
public import SerrePositivity.InfinityCategories.F1.IntervalHomFamilyProjection

/-!
概要：同じ分解三角形の Hom の次の面は、元の同じ結合比較 Hom。
方針：同じ面の厳密な族の等式を、全端点固定 Hom に移す。
規約：元の結合比較辺と同じ元の Hom 作用を保持する。
使われ方：元の第二面の Hom 輸送の分解。
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

/-- 同じ分解三角形の Hom を、同じ元の結合比較 Hom へ射影する。 -/
def cocartesianBaseChangeSecondTriangleHomSecond :
    cocartesianBaseChangeSecondTriangleHomSpace l k p q ⟶
      cocartesianBaseChangeAssociativityHomComparisonSpace l k p q :=
  intervalHomFamilyProjection (cocartesianBaseChangeSecondEquivalenceTriangle l k)
    (equivalenceTriangleFace _ 0) (cocartesianBaseChangeAssociativityHomPath l k)
    (cocartesianBaseChangeSecondEquivalenceTriangle_second l k)
    (coherentNerveVertex p) (coherentNerveVertex q)

/-- 同じ次の面への射影は、元の結合比較 Hom との同値。 -/
lemma cocartesianBaseChangeSecondTriangleHomSecond_isQCatEquivalence :
    IsQCatEquivalence (cocartesianBaseChangeSecondTriangleHomSecond l k p q) :=
  intervalHomFamilyProjection_isQCatEquivalence _ _ _ _ _ _
    (equivalenceTriangleFace_isQCatEquivalence _ 0).isFullyFaithful

/-- 同じ射影後の作用は、元の同じ結合比較 Hom の作用そのもの。 -/
lemma cocartesianBaseChangeSecondTriangleHomComparison_second :
    cocartesianBaseChangeSecondTriangleHomComparison l k p q ≫
        cocartesianBaseChangeSecondTriangleHomSecond l k p q =
      cocartesianBaseChangeAssociativityHomComparison l k p q := by
  have h := intervalHomFamilyProjection_factor
    (cocartesianBaseChangeSecondEquivalenceTriangle l k) (equivalenceTriangleFace _ 0)
    (cocartesianBaseChangeAssociativityHomPath l k)
    (cocartesianBaseChangeSecondEquivalenceTriangle_second l k)
    (coherentNerveVertex p) (coherentNerveVertex q)
  simpa only [cocartesianBaseChangeSecondTriangleHomComparison,
    cocartesianBaseChangeSecondTriangleHomSecond, cocartesianBaseChangeAssociativityHomComparison,
    Category.assoc] using congrArg (fun f ↦ coherentHomIntervalComparison p q ≫ f) h

end SerrePositivity.InfinityCategories
