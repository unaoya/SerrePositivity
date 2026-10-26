module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PiCriterion.UniverseShape
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PiCriterion.TotalPiCriterion

/-!
概要：小さい底と大きい空間値を持つ元の余錐にも、全空間比較の π 判定を適用する。
方針：底の厳密な持ち上げ同型による制限と、同宇宙の比較判定を合成する。
規約：元の余錐の native 余極限性を判定し、余錐を仮定として取り替えない。
使われ方：w = max (u+1) v における κ-filtered poset 上の最終判定の入力。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.PiCriterion

/-- 宇宙を分離した元の余錐の余極限性は、持ち上げた全空間比較の π 判定と同値。 -/
lemma isColimitCone_iff_liftedTotalPiCriterion {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{max u v + 1, u}).obj B ⟶ SpaceInfinity.{max u v})
    (c : JoinCocone F) :
    IsColimitCone c ↔
      KanMapPiCriterion (totalValueComparison (liftedBaseDiagram.{u, v} F)
        (c.restrict (liftedBaseShapeIso.{u, v} B).hom)) :=
  (isColimitCone_iff_liftedBase_restrict c).trans
    (isColimitCone_iff_totalPiCriterion (liftedBaseDiagram.{u, v} F)
      (c.restrict (liftedBaseShapeIso.{u, v} B).hom))

end SerrePositivity.InfinityCategories.F2.PiCriterion
