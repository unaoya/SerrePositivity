module

public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.Core.EquivalenceCalculus
public import SerrePositivity.InfinityCategories.F1B.Cones.SliceProjectionLaws
public import SerrePositivity.InfinityCategories.HomotopyLimits.RightConeBoundary

/-!
概要：終対象を持つ right fibration を、底の像の点の slice として表示する。
方針：終対象 slice の切断を取り、点上の slice の後合成と合成する。
規約：底への射影を厳密に保つ。Derived の宣言と集約には依存しない。
使われ方：有限形状の貼り合わせで現れる表現可能 right fibration の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 指定頂点への slice の後合成を、像の頂点に正規化する。 -/
def rightFibrationTerminalSliceMap {E B : SSet.{u}} (p : E ⟶ B) (t : E _⦋0⦌) :
    sliceOver (SSet.yonedaEquiv.symm t) ⟶
      sliceOver (SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) t)) :=
  sliceOverPostcomp _ p ≫ (eqToIso (congrArg sliceOver
    (SSet.yonedaEquiv_symm_comp t p))).hom

/-- 正規化した slice 写像は底への射影と厳密に可換する。 -/
lemma rightFibrationTerminalSliceMap_projection {E B : SSet.{u}}
    (p : E ⟶ B) (t : E _⦋0⦌) :
    rightFibrationTerminalSliceMap p t ≫ sliceOverProjection _ =
      sliceOverProjection _ ≫ p := by
  dsimp only [rightFibrationTerminalSliceMap]
  rw [Category.assoc, F1B.sliceOverProjection_eqTransport,
    F1B.sliceOverPostcomp_projection]
  exact SSet.yonedaEquiv_symm_comp t p

/-- right fibration の点上の slice の実比較は自明 Kan fibration。 -/
lemma rightFibrationTerminalSliceMap_trivialKanFibration {E B : SSet.{u}}
    (p : E ⟶ B) [RightFibration p] (t : E _⦋0⦌) :
    TrivialKanFibration (rightFibrationTerminalSliceMap p t) := by
  have := HomotopyLimits.sliceOverPostcomp_trivialKanFibration_of_rightFibration
    (SSet.yonedaEquiv.symm t) p
  exact ⟨trivialKanFibrations.comp_mem _ _ TrivialKanFibration.mem
    (MorphismProperty.rlp_of_isIso _ _)⟩

/-- 終対象を持つ right fibration は、底上で厳密な表現可能 slice 表示を持つ。 -/
lemma rightFibration_terminal_representation_exists {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [RightFibration p]
    (t : E _⦋0⦌) (ht : IsTerminalVertex t) :
    ∃ f : E ⟶ sliceOver (SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) t)),
      IsQCatEquivalence f ∧ f ≫ sliceOverProjection _ = p := by
  have : TrivialKanFibration (sliceOverProjection (SSet.yonedaEquiv.symm t)) :=
    (isTerminalVertex_iff_trivialKanFibration t).mp ht
  obtain ⟨σ, hσ⟩ := trivialKanFibration_exists_section
    (sliceOverProjection (SSet.yonedaEquiv.symm t))
  have hs := (qCatEquivalenceOfTrivialKanFibration
    (sliceOverProjection (SSet.yonedaEquiv.symm t))).isQCatEquivalence
  have hi : IsQCatEquivalence (σ ≫ sliceOverProjection _) := by
    rw [hσ]
    exact (qCatEquivalenceOfIso (Iso.refl E)).isQCatEquivalence
  have hσ' : IsQCatEquivalence σ := hs.cancel_right hi
  have := rightFibrationTerminalSliceMap_trivialKanFibration p t
  refine ⟨σ ≫ rightFibrationTerminalSliceMap p t,
    hσ'.comp (qCatEquivalenceOfTrivialKanFibration
      (rightFibrationTerminalSliceMap p t)).isQCatEquivalence, ?_⟩
  rw [Category.assoc, rightFibrationTerminalSliceMap_projection,
    ← Category.assoc, hσ, Category.id_comp]

end SerrePositivity.InfinityCategories
