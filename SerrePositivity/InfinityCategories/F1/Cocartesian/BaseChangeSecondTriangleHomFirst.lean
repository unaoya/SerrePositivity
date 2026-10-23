module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeSecondTriangleHom
public import SerrePositivity.InfinityCategories.F1.EquivalenceTriangleFaceEquivalence
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeHomPath
public import SerrePositivity.InfinityCategories.F1.IntervalMappingPostEquivalence

/-!
概要：同じ分解三角形の Hom の最初の面は、元の底変換対象の既存の比較 Hom。
方針：同じ面の頂点を元の pullback 対象へ正規化する。
規約：既存の cocartesianBaseChangeHomComparisonSpace をそのまま使う。
使われ方：元の二回目の Hom 輸送との接続。
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

/-- 同じ分解三角形の最初の面の頂点は、元の底変換対象の既存の比較 path。 -/
lemma cocartesianBaseChangeSecondEquivalenceTriangle_first_vertex
    (p : CocartesianFibrationCategory (nerve C)) :
    (equivalenceTriangleFace _ 2).app _
      ((cocartesianBaseChangeSecondEquivalenceTriangle l k).app _ (coherentNerveVertex p)) =
    (cocartesianBaseChangeHomPath l).app _
      (coherentNerveVertex ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)) := by
  have h := congrArg (fun f : CocartesianFibrationInfinity (nerve C) ⟶
    equivalencePath (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) ↦
      f.app (Opposite.op ⦋0⦌) (coherentNerveVertex p))
        (cocartesianBaseChangeSecondEquivalenceTriangle_first l k)
  exact h.trans (congrArg ((cocartesianBaseChangeHomPath l).app (Opposite.op ⦋0⦌))
    (cocartesianFibrationInfinityBaseChange_vertex (nerveMap k) p))

/-- 元の同じ分解三角形の Hom を、既存の元の二回目の比較 Hom へ射影する。 -/
def cocartesianBaseChangeSecondTriangleHomFirst
    (p q : CocartesianFibrationCategory (nerve C)) :
    cocartesianBaseChangeSecondTriangleHomSpace l k p q ⟶
      cocartesianBaseChangeHomComparisonSpace l
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q) :=
  intervalMappingPostOfEq
    (X := equivalenceTriangle
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))))
    (Y := equivalencePath
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))))
    (equivalenceTriangleFace _ 2)
    ((cocartesianBaseChangeSecondEquivalenceTriangle l k).app _ (coherentNerveVertex p))
    ((cocartesianBaseChangeSecondEquivalenceTriangle l k).app _ (coherentNerveVertex q))
    (cocartesianBaseChangeSecondEquivalenceTriangle_first_vertex l k p)
    (cocartesianBaseChangeSecondEquivalenceTriangle_first_vertex l k q)

/-- 同じ射影は、既存の元の二回目の比較 Hom との同値。 -/
lemma cocartesianBaseChangeSecondTriangleHomFirst_isQCatEquivalence
    (p q : CocartesianFibrationCategory (nerve C)) :
    IsQCatEquivalence (cocartesianBaseChangeSecondTriangleHomFirst l k p q) := by
  unfold cocartesianBaseChangeSecondTriangleHomFirst
  exact (equivalenceTriangleFace_isQCatEquivalence _ 2).isFullyFaithful
    |>.intervalMappingPostOfEq_isQCatEquivalence _ _ _ _

end SerrePositivity.InfinityCategories
