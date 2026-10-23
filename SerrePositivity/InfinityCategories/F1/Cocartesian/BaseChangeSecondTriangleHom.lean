module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeSecondEquivalenceTriangle
public import SerrePositivity.InfinityCategories.F1.CoherentHomIntervalNaturality

/-!
概要：元の第二比較を分解する三角形の Hom と、元の全相対 Hom の同じ作用。
方針：元の coherent Hom 比較と、同じ可逆三角形の全族への後合成を使う。
規約：元の全相対 Hom を保つ。
使われ方：第二面の輸送を元の二回目の底変換比較と結合比較へ戻す。
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

/-- 元の二つの fibration での同じ分解三角形の間の全 Hom。 -/
def cocartesianBaseChangeSecondTriangleHomSpace : SSet.{u + 1} :=
  intervalMappingSpace
    ((cocartesianBaseChangeSecondEquivalenceTriangle l k).app _ (coherentNerveVertex p))
    ((cocartesianBaseChangeSecondEquivalenceTriangle l k).app _ (coherentNerveVertex q))

/-- 元の同じ分解三角形の Hom は Kan 複体。 -/
instance cocartesianBaseChangeSecondTriangleHomSpace_kanComplex :
    KanComplex (cocartesianBaseChangeSecondTriangleHomSpace l k p q) := by
  change KanComplex (intervalMappingSpace
    ((cocartesianBaseChangeSecondEquivalenceTriangle l k).app _ (coherentNerveVertex p))
    ((cocartesianBaseChangeSecondEquivalenceTriangle l k).app _ (coherentNerveVertex q)))
  infer_instance

/-- 元の全相対 Hom の core を、元の同じ分解三角形の Hom へ写す。 -/
def cocartesianBaseChangeSecondTriangleHomComparison :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom p q) ⟶
      cocartesianBaseChangeSecondTriangleHomSpace l k p q :=
  coherentHomIntervalComparison p q ≫
    intervalMappingPost (cocartesianBaseChangeSecondEquivalenceTriangle l k)
      (coherentNerveVertex p) (coherentNerveVertex q)

/-- 同じ全相対 Hom の作用を展開すると、元の同じ分解三角形への後合成。 -/
lemma cocartesianBaseChangeSecondTriangleHomComparison_uncurry :
    intervalMappingUncurry (cocartesianBaseChangeSecondTriangleHomComparison l k p q) =
      intervalMappingUncurry (coherentHomIntervalComparison p q) ≫
        cocartesianBaseChangeSecondEquivalenceTriangle l k := by
  rw [cocartesianBaseChangeSecondTriangleHomComparison, intervalMappingPost_uncurry]

end SerrePositivity.InfinityCategories
