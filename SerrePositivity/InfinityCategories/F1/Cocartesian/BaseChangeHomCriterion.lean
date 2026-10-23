module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeHomSpanNaturality

/-!
概要：同じ分類 Hom 作用の底制限と、元の Hom の底変換後の作用の同値性を比較する。
方針：同じ比較 path の Hom の二射影の同値性と、厳密な二つの分解式を使う。
規約：元の全相対 Hom の作用そのものを保ち、独立な写像空間の同値で代用しない。
使われ方：元の分類 Hom 比較のセルによる降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の分類 Hom の底制限が同値であることは、元の底変換後の同じ作用の同値性と同値。 -/
lemma cocartesianStraighteningHomInterval_restrict_isQCatEquivalence_iff
    {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C)
    (p q : CocartesianFibrationCategory (nerve C)) :
    IsQCatEquivalence (cocartesianStraighteningHomInterval p q ≫
      intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k))
        (cocartesianStrictTransportCoherentDiagram p.val.hom)
        (cocartesianStrictTransportCoherentDiagram q.val.hom)) ↔
      IsQCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).map
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
          cocartesianStraighteningHomInterval
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) := by
  have : TrivialKanFibration (cocartesianBaseChangeHomSpanZero k p q) :=
    cocartesianBaseChangeHomSpanZero_trivialKanFibration k p q
  have : TrivialKanFibration (cocartesianBaseChangeHomSpanOne k p q) :=
    cocartesianBaseChangeHomSpanOne_trivialKanFibration k p q
  have h₀ := isQCatEquivalence_of_trivialKanFibration (cocartesianBaseChangeHomSpanZero k p q)
  have h₁ := isQCatEquivalence_of_trivialKanFibration (cocartesianBaseChangeHomSpanOne k p q)
  rw [← cocartesianBaseChangeHomComparison_zero, ← cocartesianBaseChangeHomComparison_one]
  constructor
  · intro h
    exact (h₀.cancel_right h).comp h₁
  · intro h
    exact (h₁.cancel_right h).comp h₀

end SerrePositivity.InfinityCategories
