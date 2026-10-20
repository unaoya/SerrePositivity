module
public import SerrePositivity.InfinityCategories.Derived.RoofTargetFunctor
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.Core.EquivalenceCalculus
public import SerrePositivity.InfinityCategories.HomotopyLimits.RightConeBoundary

/-!
概要：終対象を持つ right fibration を、底の像の点上の実 slice に同値として表示する。
方針：終対象 slice の切断と right fibration の点上の slice の自明 Kan 性を使う。
規約：底との厳密な可換性を保持する。使われ方：関手圏内の実評価の比較。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {E B : SSet.{u}} (p : E ⟶ B) (t : E _⦋0⦌)
/-- 終対象への全錐を、底の像の点上の実 slice へ送る。 -/
def roofTerminalRepresentationMap (σ : E ⟶ sliceOver (SSet.yonedaEquiv.symm t)) :
    E ⟶ sliceOver (SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) t)) :=
  σ ≫ roofTargetSliceMap p t
/-- 終対象への切断による表示は、元の底の射影と厳密に可換する。 -/
lemma roofTerminalRepresentationMap_over (σ : E ⟶ sliceOver (SSet.yonedaEquiv.symm t))
    (hσ : σ ≫ sliceOverProjection _ = 𝟙 E) :
    roofTerminalRepresentationMap p t σ ≫ sliceOverProjection _ = p := by
  rw [roofTerminalRepresentationMap, Category.assoc, roofTargetSliceMap_projection,
    ← Category.assoc, hσ, Category.id_comp]
/-- right fibration の点上の正規化した target slice 写像は自明 Kan fibration。 -/
lemma roofTargetSliceMap_trivialKanFibration [RightFibration p] :
    TrivialKanFibration (roofTargetSliceMap p t) := by
  have := HomotopyLimits.sliceOverPostcomp_trivialKanFibration_of_rightFibration
    (SSet.yonedaEquiv.symm t) p
  exact ⟨trivialKanFibrations.comp_mem _ _ TrivialKanFibration.mem
    (MorphismProperty.rlp_of_isIso _ _)⟩
/-- 終対象への切断は、同じ底の実表現可能 right fibration との同値を与える。 -/
lemma roofTerminalRepresentationMap_isQCatEquivalence [Quasicategory E] [Quasicategory B]
  [RightFibration p]
    (ht : IsTerminalVertex t) (σ : E ⟶ sliceOver (SSet.yonedaEquiv.symm t))
    (hσ : σ ≫ sliceOverProjection _ = 𝟙 E) :
    IsQCatEquivalence (roofTerminalRepresentationMap p t σ) := by
  have : TrivialKanFibration (sliceOverProjection (SSet.yonedaEquiv.symm t)) :=
    (isTerminalVertex_iff_trivialKanFibration t).mp ht
  have hs := (qCatEquivalenceOfTrivialKanFibration
    (sliceOverProjection (SSet.yonedaEquiv.symm t))).isQCatEquivalence
  have hi : IsQCatEquivalence (σ ≫ sliceOverProjection _) := by
    rw [hσ]
    exact (qCatEquivalenceOfIso (Iso.refl E)).isQCatEquivalence
  have hσ' : IsQCatEquivalence σ := hs.cancel_right hi
  have := roofTargetSliceMap_trivialKanFibration p t
  exact hσ'.comp (qCatEquivalenceOfTrivialKanFibration (roofTargetSliceMap p t)).isQCatEquivalence
/-- 終対象を持つ right fibration は、底と厳密に可換する実 slice 表示を持つ。 -/
lemma roofTerminalRepresentation_exists [Quasicategory E] [Quasicategory B] [RightFibration p]
    (ht : IsTerminalVertex t) :
    ∃ f : E ⟶ sliceOver (SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) t)),
      IsQCatEquivalence f ∧ f ≫ sliceOverProjection _ = p := by
  have : TrivialKanFibration (sliceOverProjection (SSet.yonedaEquiv.symm t)) :=
    (isTerminalVertex_iff_trivialKanFibration t).mp ht
  obtain ⟨σ, hσ⟩ := trivialKanFibration_exists_section (sliceOverProjection
    (SSet.yonedaEquiv.symm t))
  exact ⟨roofTerminalRepresentationMap p t σ,
    roofTerminalRepresentationMap_isQCatEquivalence p t ht σ hσ,
    roofTerminalRepresentationMap_over p t σ hσ⟩
end SerrePositivity.InfinityCategories
