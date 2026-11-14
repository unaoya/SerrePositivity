module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.InitialFinalComparisons.FinalHornFaceComposition
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.InitialFinalComparisons.FinalHornAppend

/-!
# 最終外側ホーンの前半全境界と後半上面の可換性

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

/-- 既知面内での最終 Path の付加は、最終区間の元の射による後合成に一致する。 -/
lemma finalHornAppend_postcomposition_viaFace (j : Fin (n + 3))
    (hj0 : 0 < j) (hjp : j < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornAppend n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace τ j
      (ne_of_lt (hjp.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n))) 0 (Fin.last (n + 2))
      (ne_of_lt hj0) (ne_of_gt (hjp.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n))) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace τ j (ne_of_lt (hjp.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n)))
      0 (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) (ne_of_lt hj0) (ne_of_gt hjp) ≫
      eHomWhiskerLeft SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ 0) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornLastArrow τ) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornAppend, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFrontThroughIso_hom_ι]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.hornHomViaFace_comp_general τ j
    (ne_of_lt (hjp.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n)))
    0 (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) (Fin.last (n + 2)) (ne_of_lt hj0)
    (ne_of_gt hjp) (ne_of_gt (hjp.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n)))]
  rw [← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom_eq_viaFace τ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)
    (Fin.last (n + 2)) (le_of_lt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n))
    (Or.inl (ne_of_gt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_pos n))) j
    (ne_of_lt (hjp.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n))) (Or.inl hjp)]
  unfold eHomWhiskerLeft
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornLastArrow_eHom]
  apply CategoryTheory.NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro F
  rfl

/-- 後半の延長が零座標面を保持すれば、その上面は前半の同じ零座標面と可換になる。 -/
lemma finalHornFrontZeroHom_postcomposition
    (g : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (Fin.last (n + 2)))) ⟶
        SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ (Fin.last (n + 2))))
    (j : Fin (n + 3)) (hj0 : 0 < j) (hjp : j < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)
    (hg : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up j)).ι ≫ g = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornInnerZeroHom τ j
      (ne_of_lt (hjp.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n))) hj0
      (hjp.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n))) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFrontZeroHom τ j hj0 hjp ≫
      eHomWhiskerLeft SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ 0) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornLastArrow τ) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up j)).ι ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornAppend n ≫ g := by
  apply CategoryTheory.NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro F
  have hcomp := congrArg (fun f ↦ f.app m F.1)
    (finalHornAppend_postcomposition_viaFace τ j hj0 hjp)
  have hzero := congrArg (fun f ↦ f.app m
    ⟨(_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornAppend n).app m F.1,
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornAppend_avoids n j
        (ne_of_lt (hjp.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n))) F.1 F.2⟩) hg
  exact hcomp.symm.trans hzero.symm

/-- 後半の延長が既知合成面を保持すれば、その上面は前半の同じ合成面と可換になる。 -/
lemma finalHornFrontCompositionHom_postcomposition
    (g : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (Fin.last (n + 2)))) ⟶
        SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ (Fin.last (n + 2))))
    (b : Fin (n + 3)) (hb0 : 0 < b) (hbp : b < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)
    (hg : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b)).ι ≫ g = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornUpperCompositionHom τ b hb0 hbp) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFrontCompositionHom τ b hb0 hbp ≫
      eHomWhiskerLeft SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ 0) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornLastArrow τ) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b)).ι ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornAppend n ≫ g := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughIso (ULift.up.{u} (0 : Fin (n + 3)))
    (ULift.up b) (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n))).hom).mp
  simp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFrontCompositionHom, ← Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornCompositionHom_on_product, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughIso_hom_ι]
  have hgProd : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up.{u} (0 : Fin (n + 3))) (ULift.up b)
      (ULift.up (Fin.last (n + 2))) ≫ g =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom τ 0 b (Fin.zero_le b) (Or.inr hbp) ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom τ b (Fin.last (n + 2)) (Fin.le_last b)
          (Or.inl (ne_of_gt hb0))) ≫
      SimplicialCategory.sHomComp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ b)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ (Fin.last (n + 2))) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughIso_hom_ι, Category.assoc, hg]
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornCompositionHom_on_product τ 0 b (Fin.last (n + 2))
      (Fin.zero_le b) (Fin.le_last b) (Or.inr hbp) (Or.inl (ne_of_gt hb0))
  unfold eHomWhiskerLeft
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornLastArrow_eHom]
  apply CategoryTheory.NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  rintro ⟨x, y⟩
  let z := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornLastPathIso.{u} n).hom.app m PUnit.unit
  have hknown := congrArg (fun f ↦ f.app m (y, z))
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom_comp τ b (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) (Fin.last (n + 2))
      (le_of_lt hbp) (le_of_lt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n))
      (Or.inl (ne_of_gt hb0)) (Or.inl (ne_of_gt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_pos n)))
      (Or.inl (ne_of_gt hb0)))
  have hfull := congrArg (fun f ↦ f.app m
    (x, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up b) (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n))
      (ULift.up (Fin.last (n + 2)))).app m (y, z))) hgProd
  change _ = g.app m ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornAppend n).app m
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up 0) (ULift.up b) (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n))).app m (x, y)))
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornAppend_comp]
  rw [show g.app m ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up 0) (ULift.up b)
      (ULift.up (Fin.last (n + 2)))).app m
        (x, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up b) (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n))
          (ULift.up (Fin.last (n + 2)))).app m (y, z))) = _ from hfull]
  change _ = (SimplicialCategory.sHomComp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ b)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ (Fin.last (n + 2)))).app m
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom τ 0 b (Fin.zero_le b) (Or.inr hbp)).app m x,
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom τ b (Fin.last (n + 2)) (Fin.le_last b)
          (Or.inl (ne_of_gt hb0))).app m
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up b) (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n))
              (ULift.up (Fin.last (n + 2)))).app m (y, z)))
  rw [show (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom τ b (Fin.last (n + 2)) (Fin.le_last b)
    (Or.inl (ne_of_gt hb0))).app m ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up b)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)) (ULift.up (Fin.last (n + 2)))).app m (y, z)) = _
      from hknown]
  exact (congrArg (fun f ↦ f.app m
    (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom τ 0 b (Fin.zero_le b) (Or.inr hbp)).app m x,
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom τ b (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) (le_of_lt hbp)
        (Or.inl (ne_of_gt hb0))).app m y),
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom τ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) (Fin.last (n + 2))
        (le_of_lt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n))
        (Or.inl (ne_of_gt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_pos n)))).app m z))
    (e_assoc' SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ b)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ (Fin.last (n + 2))))).symm

/-- 元の全既知面を保持する後半の延長は、前半の全境界と後合成に関して可換になる。 -/
lemma finalHornFrontBoundaryHom_postcomposition
    (g : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (Fin.last (n + 2)))) ⟶
        SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ (Fin.last (n + 2))))
    (hzero : ∀ (j : Fin (n + 3)) (hj0 : 0 < j) (hjn : j < Fin.last (n + 2)),
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up j)).ι ≫ g = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornInnerZeroHom τ j (ne_of_lt hjn) hj0 hjn)
    (hthrough : ∀ (b : Fin (n + 3)) (hb0 : 0 < b) (hbp : b < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n),
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b)).ι ≫ g = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornUpperCompositionHom τ b hb0 hbp) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFrontBoundaryHom τ ≫
      eHomWhiskerLeft SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ 0) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornLastArrow τ) =
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundary (show ULift.up.{u} (0 : Fin (n + 3)) <
          ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) from _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_pos n)).ι ≫
          _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornAppend n ≫ g := by
  have hj (j) : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFrontBoundaryFaceHom τ j ≫
      eHomWhiskerLeft SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ 0) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornLastArrow τ) =
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundaryFace j).ι ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornAppend n ≫ g := by
    rcases j with j | j
    · exact finalHornFrontZeroHom_postcomposition τ g j.1.down j.2.1 j.2.2
        (hzero _ j.2.1 (j.2.2.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n)))
    · exact finalHornFrontCompositionHom_postcomposition τ g j.1.down j.2.1 j.2.2
        (hthrough _ j.2.1 j.2.2)
  apply Multicofork.IsColimit.hom_ext (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundaryCover
    (show ULift.up.{u} (0 : Fin (n + 3)) < ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)
      from _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_pos n)).isColimit
  intro j
  change Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundaryFace_le _ j) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFrontBoundaryHom τ ≫
        eHomWhiskerLeft SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ 0) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornLastArrow τ)) =
    Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundaryFace_le _ j) ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundary _).ι ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornAppend n ≫ g)
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFrontBoundaryHom_on_face,
    ← Category.assoc, Subcomplex.homOfLE_ι]
  exact hj j

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
