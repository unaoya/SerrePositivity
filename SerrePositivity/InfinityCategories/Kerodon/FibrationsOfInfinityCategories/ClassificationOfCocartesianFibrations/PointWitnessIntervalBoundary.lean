module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointProductWitnessRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IntervalWitnessBoundary

/-!
概要：点上の表現空間の区間族の境界制限は trivial Kan fibration。
方針：実際の積射影上の区間境界制限を二つの厳密な同型で移す。
規約：非空性をこの段階では仮定しない。
使われ方：点上の表現空間の対角と可縮性の証明。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：積射影上の実際の表現の区間境界制限は全空間を積へ戻しても trivial Kan。
方針：区間の境界制限と引き戻し全空間の同型を合成する。
規約：点上の表現の存在は仮定しない。
使われ方：点上の表現の区間族の境界制限への移送。 -/
lemma pointProductWitnessBoundary_trivialKanFibration (E : SSet.{u + 1}) [KanComplex E] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointProductWitnessRestriction.pointProductWitnessPre E (boundary 1).ι) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.intervalWitnessRestriction_trivialKanFibration (snd E (Δ[1] : SSet.{u + 1}))
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointProductWitnessRestriction.pointProductWitnessPre]
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _ h.mem (MorphismProperty.rlp_of_isIso _ _)⟩

/-- 概要：点上の表現空間への区間族の境界制限は trivial Kan fibration。
方針：実際の区間境界制限を正規化と currying の自然性で移し、同型を消去する。
規約：全高次パラメーターで二つの境界を同時に固定する。
使われ方：Kerodon Lemma 5.6.9.2（Tag 02SR） の点上の可縮性への入力。 -/
lemma pointWitnessIntervalBoundary_trivialKanFibration (E : SSet.{u + 1}) [KanComplex E] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((pre (boundary 1).ι).app
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointProjection E))) := by
  have h := pointProductWitnessBoundary_trivialKanFibration E
  have hcomp := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointProductWitnessTensorIso E (boundary 1)).hom
    h.mem (MorphismProperty.rlp_of_isIso _ _)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointProductWitnessRestriction.pointProductWitnessTensorIso_hom_naturality] at hcomp
  exact ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.cancel_left_of_respectsIso _ _).mp hcomp⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
