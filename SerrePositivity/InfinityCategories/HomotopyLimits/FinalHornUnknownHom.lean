module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FinalHornBoundaryCompatibility

/-!
# 最終外側ホーンの二つの未知 Hom の構成

概要：実際の最終外側ホーンの未知二区間の Hom を元の面データから構成する。
方針：native Path の合成と元の既知面の合成保存則を使う。
規約：全境界の可換性は証明し、Cartesian 性と実際の候補辺の同定は別に行う。
使われ方：HTT 5.2.4.6 の相対外側ホーン充填。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Limits MonoidalCategory SSet
open CategoryTheory.SimplicialThickening
open SerrePositivity.InfinityCategories.Coherent
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
variable {n : ℕ}
  (τ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ SimplicialNerve C)

/-- 前半の元の全境界を固定し、後半の上面を実際の最終区間の後合成に沿って持ち上げる。 -/
lemma finalHornFrontHom_extension
    [TrivialKanFibration (eHomWhiskerLeft SSet (hornObj τ 0) (finalHornLastArrow τ))]
    (g : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (Fin.last (n + 2)))) ⟶
        SimplicialCategory.sHom (hornObj τ 0) (hornObj τ (Fin.last (n + 2))))
    (hzero : ∀ (j : Fin (n + 3)) (hj0 : 0 < j) (hjn : j < Fin.last (n + 2)),
      (pathAvoids (ULift.up j)).ι ≫ g = hornInnerZeroHom τ j (ne_of_lt hjn) hj0 hjn)
    (hthrough : ∀ (b : Fin (n + 3)) (hb0 : 0 < b) (hbp : b < finalHornPenultimate n),
      (pathThrough (ULift.up b)).ι ≫ g = finalHornUpperCompositionHom τ b hb0 hbp) :
    ∃ f : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (finalHornPenultimate n))) ⟶
        SimplicialCategory.sHom (hornObj τ 0) (hornObj τ (finalHornPenultimate n)),
      (∀ j, (pathCubeBoundaryFace j).ι ≫ f = finalHornFrontBoundaryFaceHom τ j) ∧
      f ≫ eHomWhiskerLeft SSet (hornObj τ 0) (finalHornLastArrow τ) =
        finalHornAppend n ≫ g :=
  finalHornFrontBoundaryHom_lift τ _ _
    (finalHornFrontBoundaryHom_postcomposition τ g hzero hthrough)

/-- 元の最終外側ホーンの二つの未知 Hom を、全既知面と上面の合成式を保持して構成する。 -/
lemma finalHornUnknownHom_extension
    [KanComplex (SimplicialCategory.sHom (hornObj τ 0) (hornObj τ (Fin.last (n + 2))))]
    [TrivialKanFibration (eHomWhiskerLeft SSet (hornObj τ 0) (finalHornLastArrow τ))] :
    ∃ g : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (Fin.last (n + 2)))) ⟶
        SimplicialCategory.sHom (hornObj τ 0) (hornObj τ (Fin.last (n + 2))),
      (∀ (j : Fin (n + 3)) (hj0 : 0 < j) (hjn : j < Fin.last (n + 2)),
        (pathAvoids (ULift.up j)).ι ≫ g = hornInnerZeroHom τ j (ne_of_lt hjn) hj0 hjn) ∧
      (∀ (b : Fin (n + 3)) (hb0 : 0 < b) (hbp : b < finalHornPenultimate n),
        (pathThrough (ULift.up b)).ι ≫ g = finalHornUpperCompositionHom τ b hb0 hbp) ∧
      ∃ f : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
        (ULift.up (finalHornPenultimate n))) ⟶
          SimplicialCategory.sHom (hornObj τ 0) (hornObj τ (finalHornPenultimate n)),
        (∀ j, (pathCubeBoundaryFace j).ι ≫ f = finalHornFrontBoundaryFaceHom τ j) ∧
        f ≫ eHomWhiskerLeft SSet (hornObj τ 0) (finalHornLastArrow τ) =
          finalHornAppend n ≫ g := by
  obtain ⟨g, hzero, hthrough⟩ := finalHornHollowHom_extension_components τ
  exact ⟨g, hzero, hthrough, finalHornFrontHom_extension τ g hzero hthrough⟩

/-- 後合成との可換性から、後半の penultimate 合成面の元の合成式を回収する。 -/
lemma finalHornFrontHom_postcomposition_composition
    (g : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (Fin.last (n + 2)))) ⟶
        SimplicialCategory.sHom (hornObj τ 0) (hornObj τ (Fin.last (n + 2))))
    (f : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (finalHornPenultimate n))) ⟶
        SimplicialCategory.sHom (hornObj τ 0) (hornObj τ (finalHornPenultimate n)))
    (h : f ≫ eHomWhiskerLeft SSet (hornObj τ 0) (finalHornLastArrow τ) =
      finalHornAppend n ≫ g) :
    (pathThrough (ULift.up (finalHornPenultimate n))).ι ≫ g =
      (pathThroughIso (ULift.up.{u} (0 : Fin (n + 3)))
        (ULift.up (finalHornPenultimate n)) (ULift.up (Fin.last (n + 2)))).inv ≫
          (f ⊗ₘ finalHornKnownIntervalHom τ (finalHornPenultimate n) (Fin.last (n + 2))
            (le_of_lt (finalHornPenultimate_lt_last n))
            (Or.inl (ne_of_gt (finalHornPenultimate_pos n)))) ≫
              SimplicialCategory.sHomComp (hornObj τ 0)
                (hornObj τ (finalHornPenultimate n)) (hornObj τ (Fin.last (n + 2))) := by
  apply (cancel_epi (finalHornFrontThroughIso n).hom).mp
  rw [finalHornFrontThroughIso_postcomposition]
  exact h.symm

end
end SerrePositivity.InfinityCategories.HomotopyLimits
