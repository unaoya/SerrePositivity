module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FinalHornFaceComposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.FinalHornAppend

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
open SerrePositivity.InfinityCategories.Coherent
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
variable {n : ℕ}
  (τ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ SimplicialNerve C)

/-- 既知面内での最終 Path の付加は、最終区間の元の射による後合成に一致する。 -/
lemma finalHornAppend_postcomposition_viaFace (j : Fin (n + 3))
    (hj0 : 0 < j) (hjp : j < finalHornPenultimate n) :
    finalHornAppend n ≫ hornHomViaFace τ j
      (ne_of_lt (hjp.trans (finalHornPenultimate_lt_last n))) 0 (Fin.last (n + 2))
      (ne_of_lt hj0) (ne_of_gt (hjp.trans (finalHornPenultimate_lt_last n))) =
    hornHomViaFace τ j (ne_of_lt (hjp.trans (finalHornPenultimate_lt_last n)))
      0 (finalHornPenultimate n) (ne_of_lt hj0) (ne_of_gt hjp) ≫
      eHomWhiskerLeft SSet (hornObj τ 0) (finalHornLastArrow τ) := by
  rw [finalHornAppend, finalHornFrontThroughIso_hom_ι]
  simp only [Category.assoc]
  rw [hornHomViaFace_comp_general τ j
    (ne_of_lt (hjp.trans (finalHornPenultimate_lt_last n)))
    0 (finalHornPenultimate n) (Fin.last (n + 2)) (ne_of_lt hj0)
    (ne_of_gt hjp) (ne_of_gt (hjp.trans (finalHornPenultimate_lt_last n)))]
  rw [← finalHornKnownIntervalHom_eq_viaFace τ (finalHornPenultimate n)
    (Fin.last (n + 2)) (le_of_lt (finalHornPenultimate_lt_last n))
    (Or.inl (ne_of_gt (finalHornPenultimate_pos n))) j
    (ne_of_lt (hjp.trans (finalHornPenultimate_lt_last n))) (Or.inl hjp)]
  unfold eHomWhiskerLeft
  rw [finalHornLastArrow_eHom]
  apply CategoryTheory.NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro F
  rfl

/-- 後半の延長が零座標面を保持すれば、その上面は前半の同じ零座標面と可換になる。 -/
lemma finalHornFrontZeroHom_postcomposition
    (g : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (Fin.last (n + 2)))) ⟶
        SimplicialCategory.sHom (hornObj τ 0) (hornObj τ (Fin.last (n + 2))))
    (j : Fin (n + 3)) (hj0 : 0 < j) (hjp : j < finalHornPenultimate n)
    (hg : (pathAvoids (ULift.up j)).ι ≫ g = hornInnerZeroHom τ j
      (ne_of_lt (hjp.trans (finalHornPenultimate_lt_last n))) hj0
      (hjp.trans (finalHornPenultimate_lt_last n))) :
    finalHornFrontZeroHom τ j hj0 hjp ≫
      eHomWhiskerLeft SSet (hornObj τ 0) (finalHornLastArrow τ) =
        (pathAvoids (ULift.up j)).ι ≫ finalHornAppend n ≫ g := by
  apply CategoryTheory.NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro F
  have hcomp := congrArg (fun f ↦ f.app m F.1)
    (finalHornAppend_postcomposition_viaFace τ j hj0 hjp)
  have hzero := congrArg (fun f ↦ f.app m
    ⟨(finalHornAppend n).app m F.1,
      finalHornAppend_avoids n j
        (ne_of_lt (hjp.trans (finalHornPenultimate_lt_last n))) F.1 F.2⟩) hg
  exact hcomp.symm.trans hzero.symm

/-- 後半の延長が既知合成面を保持すれば、その上面は前半の同じ合成面と可換になる。 -/
lemma finalHornFrontCompositionHom_postcomposition
    (g : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (Fin.last (n + 2)))) ⟶
        SimplicialCategory.sHom (hornObj τ 0) (hornObj τ (Fin.last (n + 2))))
    (b : Fin (n + 3)) (hb0 : 0 < b) (hbp : b < finalHornPenultimate n)
    (hg : (pathThrough (ULift.up b)).ι ≫ g = finalHornUpperCompositionHom τ b hb0 hbp) :
    finalHornFrontCompositionHom τ b hb0 hbp ≫
      eHomWhiskerLeft SSet (hornObj τ 0) (finalHornLastArrow τ) =
        (pathThrough (ULift.up b)).ι ≫ finalHornAppend n ≫ g := by
  apply (cancel_epi (pathThroughIso (ULift.up.{u} (0 : Fin (n + 3)))
    (ULift.up b) (ULift.up (finalHornPenultimate n))).hom).mp
  simp only [finalHornFrontCompositionHom, ← Category.assoc]
  rw [finalHornCompositionHom_on_product, pathThroughIso_hom_ι]
  have hgProd : pathCompMap (ULift.up.{u} (0 : Fin (n + 3))) (ULift.up b)
      (ULift.up (Fin.last (n + 2))) ≫ g =
      (finalHornKnownIntervalHom τ 0 b (Fin.zero_le b) (Or.inr hbp) ⊗ₘ
        finalHornKnownIntervalHom τ b (Fin.last (n + 2)) (Fin.le_last b)
          (Or.inl (ne_of_gt hb0))) ≫
      SimplicialCategory.sHomComp (hornObj τ 0) (hornObj τ b)
        (hornObj τ (Fin.last (n + 2))) := by
    rw [← pathThroughIso_hom_ι, Category.assoc, hg]
    exact finalHornCompositionHom_on_product τ 0 b (Fin.last (n + 2))
      (Fin.zero_le b) (Fin.le_last b) (Or.inr hbp) (Or.inl (ne_of_gt hb0))
  unfold eHomWhiskerLeft
  rw [finalHornLastArrow_eHom]
  apply CategoryTheory.NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  rintro ⟨x, y⟩
  let z := (finalHornLastPathIso.{u} n).hom.app m PUnit.unit
  have hknown := congrArg (fun f ↦ f.app m (y, z))
    (finalHornKnownIntervalHom_comp τ b (finalHornPenultimate n) (Fin.last (n + 2))
      (le_of_lt hbp) (le_of_lt (finalHornPenultimate_lt_last n))
      (Or.inl (ne_of_gt hb0)) (Or.inl (ne_of_gt (finalHornPenultimate_pos n)))
      (Or.inl (ne_of_gt hb0)))
  have hfull := congrArg (fun f ↦ f.app m
    (x, (pathCompMap (ULift.up b) (ULift.up (finalHornPenultimate n))
      (ULift.up (Fin.last (n + 2)))).app m (y, z))) hgProd
  change _ = g.app m ((finalHornAppend n).app m
    ((pathCompMap (ULift.up 0) (ULift.up b) (ULift.up (finalHornPenultimate n))).app m (x, y)))
  rw [finalHornAppend_comp]
  rw [show g.app m ((pathCompMap (ULift.up 0) (ULift.up b)
      (ULift.up (Fin.last (n + 2)))).app m
        (x, (pathCompMap (ULift.up b) (ULift.up (finalHornPenultimate n))
          (ULift.up (Fin.last (n + 2)))).app m (y, z))) = _ from hfull]
  change _ = (SimplicialCategory.sHomComp (hornObj τ 0) (hornObj τ b)
    (hornObj τ (Fin.last (n + 2)))).app m
      ((finalHornKnownIntervalHom τ 0 b (Fin.zero_le b) (Or.inr hbp)).app m x,
        (finalHornKnownIntervalHom τ b (Fin.last (n + 2)) (Fin.le_last b)
          (Or.inl (ne_of_gt hb0))).app m
            ((pathCompMap (ULift.up b) (ULift.up (finalHornPenultimate n))
              (ULift.up (Fin.last (n + 2)))).app m (y, z)))
  rw [show (finalHornKnownIntervalHom τ b (Fin.last (n + 2)) (Fin.le_last b)
    (Or.inl (ne_of_gt hb0))).app m ((pathCompMap (ULift.up b)
      (ULift.up (finalHornPenultimate n)) (ULift.up (Fin.last (n + 2)))).app m (y, z)) = _
      from hknown]
  exact (congrArg (fun f ↦ f.app m
    (((finalHornKnownIntervalHom τ 0 b (Fin.zero_le b) (Or.inr hbp)).app m x,
      (finalHornKnownIntervalHom τ b (finalHornPenultimate n) (le_of_lt hbp)
        (Or.inl (ne_of_gt hb0))).app m y),
      (finalHornKnownIntervalHom τ (finalHornPenultimate n) (Fin.last (n + 2))
        (le_of_lt (finalHornPenultimate_lt_last n))
        (Or.inl (ne_of_gt (finalHornPenultimate_pos n)))).app m z))
    (e_assoc' SSet (hornObj τ 0) (hornObj τ b)
      (hornObj τ (finalHornPenultimate n)) (hornObj τ (Fin.last (n + 2))))).symm

/-- 元の全既知面を保持する後半の延長は、前半の全境界と後合成に関して可換になる。 -/
lemma finalHornFrontBoundaryHom_postcomposition
    (g : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (Fin.last (n + 2)))) ⟶
        SimplicialCategory.sHom (hornObj τ 0) (hornObj τ (Fin.last (n + 2))))
    (hzero : ∀ (j : Fin (n + 3)) (hj0 : 0 < j) (hjn : j < Fin.last (n + 2)),
      (pathAvoids (ULift.up j)).ι ≫ g = hornInnerZeroHom τ j (ne_of_lt hjn) hj0 hjn)
    (hthrough : ∀ (b : Fin (n + 3)) (hb0 : 0 < b) (hbp : b < finalHornPenultimate n),
      (pathThrough (ULift.up b)).ι ≫ g = finalHornUpperCompositionHom τ b hb0 hbp) :
    finalHornFrontBoundaryHom τ ≫
      eHomWhiskerLeft SSet (hornObj τ 0) (finalHornLastArrow τ) =
        (pathCubeBoundary (show ULift.up.{u} (0 : Fin (n + 3)) <
          ULift.up (finalHornPenultimate n) from finalHornPenultimate_pos n)).ι ≫
          finalHornAppend n ≫ g := by
  have hj (j) : finalHornFrontBoundaryFaceHom τ j ≫
      eHomWhiskerLeft SSet (hornObj τ 0) (finalHornLastArrow τ) =
        (pathCubeBoundaryFace j).ι ≫ finalHornAppend n ≫ g := by
    rcases j with j | j
    · exact finalHornFrontZeroHom_postcomposition τ g j.1.down j.2.1 j.2.2
        (hzero _ j.2.1 (j.2.2.trans (finalHornPenultimate_lt_last n)))
    · exact finalHornFrontCompositionHom_postcomposition τ g j.1.down j.2.1 j.2.2
        (hthrough _ j.2.1 j.2.2)
  apply Multicofork.IsColimit.hom_ext (pathCubeBoundaryCover
    (show ULift.up.{u} (0 : Fin (n + 3)) < ULift.up (finalHornPenultimate n)
      from finalHornPenultimate_pos n)).isColimit
  intro j
  change Subcomplex.homOfLE (pathCubeBoundaryFace_le _ j) ≫
      (finalHornFrontBoundaryHom τ ≫
        eHomWhiskerLeft SSet (hornObj τ 0) (finalHornLastArrow τ)) =
    Subcomplex.homOfLE (pathCubeBoundaryFace_le _ j) ≫
      ((pathCubeBoundary _).ι ≫ finalHornAppend n ≫ g)
  rw [← Category.assoc, finalHornFrontBoundaryHom_on_face,
    ← Category.assoc, Subcomplex.homOfLE_ι]
  exact hj j

end
end SerrePositivity.InfinityCategories.HomotopyLimits
