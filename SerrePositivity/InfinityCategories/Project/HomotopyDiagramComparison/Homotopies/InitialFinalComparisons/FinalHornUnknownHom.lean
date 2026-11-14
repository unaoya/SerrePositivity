module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.InitialFinalComparisons.FinalHornBoundaryCompatibility

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

open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
variable {n : ℕ}
  (τ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ SimplicialNerve C)

/-- 前半の元の全境界を固定し、後半の上面を実際の最終区間の後合成に沿って持ち上げる。 -/
lemma finalHornFrontHom_extension
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (eHomWhiskerLeft SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ 0) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornLastArrow τ))]
    (g : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (Fin.last (n + 2)))) ⟶
        SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ (Fin.last (n + 2))))
    (hzero : ∀ (j : Fin (n + 3)) (hj0 : 0 < j) (hjn : j < Fin.last (n + 2)),
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up j)).ι ≫ g = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornInnerZeroHom τ j (ne_of_lt hjn) hj0 hjn)
    (hthrough : ∀ (b : Fin (n + 3)) (hb0 : 0 < b) (hbp : b < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n),
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b)).ι ≫ g = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornUpperCompositionHom τ b hb0 hbp) :
    ∃ f : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n))) ⟶
        SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)),
      (∀ j, (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundaryFace j).ι ≫ f = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFrontBoundaryFaceHom τ j) ∧
      f ≫ eHomWhiskerLeft SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ 0) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornLastArrow τ) =
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornAppend n ≫ g :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFrontBoundaryHom_lift τ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFrontBoundaryHom_postcomposition τ g hzero hthrough)

/-- 元の最終外側ホーンの二つの未知 Hom を、全既知面と上面の合成式を保持して構成する。 -/
lemma finalHornUnknownHom_extension
    [KanComplex (SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ (Fin.last (n + 2))))]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (eHomWhiskerLeft SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ 0) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornLastArrow τ))] :
    ∃ g : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (Fin.last (n + 2)))) ⟶
        SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ (Fin.last (n + 2))),
      (∀ (j : Fin (n + 3)) (hj0 : 0 < j) (hjn : j < Fin.last (n + 2)),
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up j)).ι ≫ g = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornInnerZeroHom τ j (ne_of_lt hjn) hj0 hjn) ∧
      (∀ (b : Fin (n + 3)) (hb0 : 0 < b) (hbp : b < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n),
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b)).ι ≫ g = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornUpperCompositionHom τ b hb0 hbp) ∧
      ∃ f : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n))) ⟶
          SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)),
        (∀ j, (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundaryFace j).ι ≫ f = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFrontBoundaryFaceHom τ j) ∧
        f ≫ eHomWhiskerLeft SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ 0) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornLastArrow τ) =
          _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornAppend n ≫ g := by
  obtain ⟨g, hzero, hthrough⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornHollowHom_extension_components τ
  exact ⟨g, hzero, hthrough, finalHornFrontHom_extension τ g hzero hthrough⟩

/-- 後合成との可換性から、後半の penultimate 合成面の元の合成式を回収する。 -/
lemma finalHornFrontHom_postcomposition_composition
    (g : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (Fin.last (n + 2)))) ⟶
        SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ (Fin.last (n + 2))))
    (f : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n))) ⟶
        SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)))
    (h : f ≫ eHomWhiskerLeft SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ 0) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornLastArrow τ) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornAppend n ≫ g) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n))).ι ≫ g =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughIso (ULift.up.{u} (0 : Fin (n + 3)))
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)) (ULift.up (Fin.last (n + 2)))).inv ≫
          (f ⊗ₘ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom τ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) (Fin.last (n + 2))
            (le_of_lt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n))
            (Or.inl (ne_of_gt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_pos n)))) ≫
              SimplicialCategory.sHomComp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ 0)
                (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ (Fin.last (n + 2))) := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFrontThroughIso n).hom).mp
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFrontThroughIso_postcomposition]
  exact h.symm

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
