module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeSecondHomSpan
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeTriangleHomEquivalence
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalHomFamilyProjection
public import SerrePositivity.InfinityCategories.F1.Coherent.HomIntervalNaturality

/-!
概要：元の比較三角形の Hom を、元の同じ第二面の Hom へ射影する。
方針：同じ面の族への厳密な制限を、元の全 Hom へ移す。
規約：元の比較三角形と元の全相対 Hom を保持する。
使われ方：第二面の元の二段の輸送を、元の三角形則へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 同じ元の比較三角形の Hom の第二面への射影。 -/
def cocartesianBaseChangeTriangleHomSecond :
    cocartesianBaseChangeTriangleHomSpace l k p q ⟶
      cocartesianBaseChangeSecondHomComparisonSpace l k p q :=
  intervalHomFamilyProjection (cocartesianBaseChangeEquivalenceTriangle l k)
    (equivalenceTriangleFace _ 0) (cocartesianBaseChangeSecondHomPath l k) rfl
    (coherentNerveVertex p) (coherentNerveVertex q)

/-- 同じ第二面への Hom 射影は同値。 -/
lemma cocartesianBaseChangeTriangleHomSecond_isQCatEquivalence :
    IsQCatEquivalence (cocartesianBaseChangeTriangleHomSecond l k p q) :=
  intervalHomFamilyProjection_isQCatEquivalence _ _ _ _ _ _
    (equivalenceTriangleFace_isQCatEquivalence _ 0).isFullyFaithful

/-- 同じ元の全相対 Hom の第二面の作用は、元の同じ path への後合成そのもの。 -/
lemma cocartesianBaseChangeTriangleHomComparison_second :
    cocartesianBaseChangeTriangleHomComparison l k p q ≫
        cocartesianBaseChangeTriangleHomSecond l k p q =
      coherentHomIntervalComparison p q ≫ intervalMappingPost
        (cocartesianBaseChangeSecondHomPath l k)
        (coherentNerveVertex p) (coherentNerveVertex q) := by
  have h := intervalHomFamilyProjection_factor (cocartesianBaseChangeEquivalenceTriangle l k)
    (equivalenceTriangleFace _ 0) (cocartesianBaseChangeSecondHomPath l k) rfl
    (coherentNerveVertex p) (coherentNerveVertex q)
  simpa only [cocartesianBaseChangeTriangleHomComparison, coherentHomIntervalComparison,
    cocartesianBaseChangeTriangleHomSecond, Category.assoc] using
      congrArg (fun f ↦ coherentHomIntervalComparison p q ≫ f) h

end SerrePositivity.InfinityCategories
