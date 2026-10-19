module

public import SerrePositivity.InfinityCategories.F1.PointProductWitnessRestriction
public import SerrePositivity.InfinityCategories.F1.IntervalWitnessBoundary

/-!
概要：点上の表現空間の区間族の境界制限は trivial Kan fibration。
方針：実際の積射影上の区間境界制限を二つの厳密な同型で移す。
規約：非空性をこの段階では仮定しない。
使われ方：点上の表現空間の対角と可縮性の証明。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：積射影上の実際の表現の区間境界制限は全空間を積へ戻しても trivial Kan。
方針：区間の境界制限と引き戻し全空間の同型を合成する。
規約：点上の表現の存在は仮定しない。
使われ方：点上の表現の区間族の境界制限への移送。 -/
lemma pointProductWitnessBoundary_trivialKanFibration (E : SSet.{u + 1}) [KanComplex E] :
    TrivialKanFibration (pointProductWitnessPre E (boundary 1).ι) := by
  have h := intervalWitnessRestriction_trivialKanFibration (snd E (Δ[1] : SSet.{u + 1}))
  dsimp only [pointProductWitnessPre]
  exact ⟨trivialKanFibrations.comp_mem _ _ h.mem (MorphismProperty.rlp_of_isIso _ _)⟩

/-- 概要：点上の表現空間への区間族の境界制限は trivial Kan fibration。
方針：実際の区間境界制限を正規化と currying の自然性で移し、同型を消去する。
規約：全高次パラメーターで二つの境界を同時に固定する。
使われ方：Kerodon Lemma 5.6.9.2 の点上の可縮性への入力。 -/
lemma pointWitnessIntervalBoundary_trivialKanFibration (E : SSet.{u + 1}) [KanComplex E] :
    TrivialKanFibration ((pre (boundary 1).ι).app
      (transportWitnessSpace (transportPointProjection E))) := by
  have h := pointProductWitnessBoundary_trivialKanFibration E
  have hcomp := trivialKanFibrations.comp_mem _ (pointProductWitnessTensorIso E (boundary 1)).hom
    h.mem (MorphismProperty.rlp_of_isIso _ _)
  rw [pointProductWitnessTensorIso_hom_naturality] at hcomp
  exact ⟨(trivialKanFibrations.cancel_left_of_respectsIso _ _).mp hcomp⟩

end SerrePositivity.InfinityCategories
