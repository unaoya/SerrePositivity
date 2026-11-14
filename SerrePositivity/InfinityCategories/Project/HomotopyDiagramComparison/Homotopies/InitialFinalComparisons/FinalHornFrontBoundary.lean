module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.PathCubeBoundaryCover
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.InitialFinalComparisons.FinalHornHollow

/-!
# 最終外側ホーンからの前半 Hom の全境界回収

概要：元の最終外側ホーンの未知 Hom を構成するための境界データを保持する。
方針：native Path の座標面と元の面制限を使う。
規約：未知二区間を区別し、小次元の空境界も保持する。
使われ方：HTT 5.2.4.6 の相対外側ホーン充填。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open CategoryTheory.SimplicialThickening

open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {n : ℕ}
  (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ SimplicialNerve C)

/-- 元の最終ホーンの既知面から、前半未知 Hom の零座標面を回収する。 -/
def finalHornFrontZeroHom (j : Fin (n + 3)) (hj0 : 0 < j)
    (hjp : j < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up.{u} (0 : Fin (n + 3)))
      (b := ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)) (ULift.up j) : SSet) ⟶
        SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up j)).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace σ j
    (ne_of_lt (hjp.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n))) 0 (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)
    (ne_of_lt hj0) (ne_of_gt hjp)

/-- 元のホーンの二つの前半零座標面は、その交わりで一致する。 -/
lemma finalHornFrontZeroHom_overlap (j k : Fin (n + 3))
    (hj0 : 0 < j) (hjp : j < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)
    (hk0 : 0 < k) (hkp : k < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) :
    SSet.Subcomplex.homOfLE
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up.{u} (0 : Fin (n + 3)))
        (b := ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)) (ULift.up j) ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up k) ≤
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up j) from inf_le_left) ≫ finalHornFrontZeroHom σ j hj0 hjp =
    SSet.Subcomplex.homOfLE
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up.{u} (0 : Fin (n + 3)))
        (b := ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)) (ULift.up j) ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up k) ≤
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up k) from inf_le_right) ≫ finalHornFrontZeroHom σ k hk0 hkp := by
  simp only [finalHornFrontZeroHom, ← Category.assoc, SSet.Subcomplex.homOfLE_ι]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace_zero_overlap_general σ j k
    (ne_of_lt (hjp.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n)))
    (ne_of_lt (hkp.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n))) 0 (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)
    (ne_of_lt hj0) (ne_of_gt hjp) (ne_of_lt hk0) (ne_of_gt hkp)

/-- 二つの既知区間の合成から、前半未知 Hom の合成面を回収する。 -/
def finalHornFrontCompositionHom (b : Fin (n + 3)) (hb0 : 0 < b)
    (hbp : b < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := ULift.up.{u} (0 : Fin (n + 3)))
      (c := ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)) (ULift.up b) : SSet) ⟶
        SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornCompositionHom σ 0 b (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) (Fin.zero_le b) (le_of_lt hbp)
    (Or.inr hbp) (Or.inl (ne_of_gt hb0))

/-- 前半の零座標面と合成面の一致を元のホーンの整合性から導く。 -/
lemma finalHornFrontZeroHom_composition_overlap (j b : Fin (n + 3))
    (hj0 : 0 < j) (hjp : j < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)
    (hb0 : 0 < b) (hbp : b < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) :
    SSet.Subcomplex.homOfLE
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up.{u} (0 : Fin (n + 3)))
        (b := ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)) (ULift.up j) ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b) ≤
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up j) from inf_le_left) ≫ finalHornFrontZeroHom σ j hj0 hjp =
    SSet.Subcomplex.homOfLE
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up.{u} (0 : Fin (n + 3)))
        (b := ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)) (ULift.up j) ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b) ≤
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b) from inf_le_right) ≫
      finalHornFrontCompositionHom σ b hb0 hbp := by
  by_cases hbj : b = j
  · subst b
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathMixed_self_hom_ext _ _ _ _ _
  simp only [finalHornFrontZeroHom, ← Category.assoc, SSet.Subcomplex.homOfLE_ι]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornCompositionHom_zero_overlap_general σ j
    (ne_of_lt (hjp.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n)))
    0 b (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) (ne_of_lt hj0) hbj (ne_of_gt hjp)
    (Fin.zero_le b) (le_of_lt hbp) (Or.inr hbp) (Or.inl (ne_of_gt hb0))

/-- 前半の二つの合成面の一致を元の既知区間の合成則から導く。 -/
lemma finalHornFrontCompositionHom_overlap (b c : Fin (n + 3))
    (hb0 : 0 < b) (hbp : b < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)
    (hc0 : 0 < c) (hcp : c < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) :
    SSet.Subcomplex.homOfLE
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := ULift.up.{u} (0 : Fin (n + 3)))
        (c := ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)) (ULift.up b) ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up c) ≤
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b) from inf_le_left) ≫ finalHornFrontCompositionHom σ b hb0 hbp =
    SSet.Subcomplex.homOfLE
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := ULift.up.{u} (0 : Fin (n + 3)))
        (c := ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)) (ULift.up b) ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up c) ≤
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up c) from inf_le_right) ≫
      finalHornFrontCompositionHom σ c hc0 hcp := by
  rcases le_total b c with hbc | hcb
  · exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornCompositionHom_composition_overlap σ 0 b c (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)
      (Fin.zero_le b) hbc (le_of_lt hcp) (Or.inr hbp) (Or.inl (ne_of_gt hb0))
      (Or.inl (ne_of_gt hc0)) (Or.inr hcp) (Or.inl (ne_of_gt hb0))
  · have he := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornCompositionHom_composition_overlap σ 0 c b (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)
      (Fin.zero_le c) hcb (le_of_lt hbp) (Or.inr hcp) (Or.inl (ne_of_gt hc0))
      (Or.inl (ne_of_gt hb0)) (Or.inr hbp) (Or.inl (ne_of_gt hc0))
    apply CategoryTheory.NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro F
    exact (congrArg (fun k ↦ k.app m ⟨F.1, ⟨F.2.2, F.2.1⟩⟩) he).symm

/-- 前半未知 Hom の全座標面の写像を元の最終外側ホーンから回収する。 -/
def finalHornFrontBoundaryFaceHom :
    ∀ j, (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundaryFace (a := ULift.up.{u} (0 : Fin (n + 3)))
      (b := ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)) j : SSet) ⟶
        SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)) := by
  intro j
  rcases j with j | j
  · exact finalHornFrontZeroHom σ j.1.down j.2.1 j.2.2
  · exact finalHornFrontCompositionHom σ j.1.down j.2.1 j.2.2

/-- 回収した全座標面の交わりでの一致を導き、追加仮定にしない。 -/
lemma finalHornFrontBoundaryFaceHom_compatible :
    ∀ j k, SSet.Subcomplex.homOfLE
      (show _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundaryFace (a := ULift.up.{u} (0 : Fin (n + 3)))
        (b := ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)) j ⊓ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundaryFace k ≤
          _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundaryFace j from inf_le_left) ≫ finalHornFrontBoundaryFaceHom σ j =
      SSet.Subcomplex.homOfLE
      (show _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundaryFace (a := ULift.up.{u} (0 : Fin (n + 3)))
        (b := ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)) j ⊓ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundaryFace k ≤
          _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundaryFace k from inf_le_right) ≫ finalHornFrontBoundaryFaceHom σ k := by
  rintro (j | j) (k | k)
  · exact finalHornFrontZeroHom_overlap σ j.1.down k.1.down j.2.1 j.2.2 k.2.1 k.2.2
  · exact finalHornFrontZeroHom_composition_overlap σ j.1.down k.1.down j.2.1 j.2.2 k.2.1 k.2.2
  · have he := finalHornFrontZeroHom_composition_overlap σ k.1.down j.1.down
      k.2.1 k.2.2 j.2.1 j.2.2
    apply CategoryTheory.NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro F
    exact (congrArg (fun f ↦ f.app m ⟨F.1, ⟨F.2.2, F.2.1⟩⟩) he).symm
  · exact finalHornFrontCompositionHom_overlap σ j.1.down k.1.down j.2.1 j.2.2 k.2.1 k.2.2

/-- 元の最終外側ホーンから、前半未知 Hom の全境界写像を貼り合わせる。 -/
def finalHornFrontBoundaryHom :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundary
      (show ULift.up.{u} (0 : Fin (n + 3)) < ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)
        from _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_pos n) : SSet) ⟶
          SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundaryGlue _ (finalHornFrontBoundaryFaceHom σ)
    (finalHornFrontBoundaryFaceHom_compatible σ)

/-- 前半の全境界写像は元の各零座標面と各合成面を保持する。 -/
lemma finalHornFrontBoundaryHom_on_face (j) :
    SSet.Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundaryFace_le
      (show ULift.up.{u} (0 : Fin (n + 3)) < ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)
        from _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_pos n) j) ≫ finalHornFrontBoundaryHom σ =
      finalHornFrontBoundaryFaceHom σ j :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundaryGlue_on_face _ _ _ j

/-- 前半の元の全境界を固定して、可換な底の写像を trivial Kan 射に沿って持ち上げる。 -/
lemma finalHornFrontBoundaryHom_lift {Y : SSet.{u}}
    (p : SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)) ⟶ Y)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p]
    (g : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n))) ⟶ Y)
    (h : finalHornFrontBoundaryHom σ ≫ p = (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundary
      (show ULift.up.{u} (0 : Fin (n + 3)) < ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)
        from _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_pos n)).ι ≫ g) :
    ∃ l : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n))) ⟶
        SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)),
      (∀ j, (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundaryFace j).ι ≫ l = finalHornFrontBoundaryFaceHom σ j) ∧ l ≫ p = g := by
  have hj (j) : finalHornFrontBoundaryFaceHom σ j ≫ p = (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundaryFace j).ι ≫ g := by
    rw [← finalHornFrontBoundaryHom_on_face σ j, Category.assoc, h, ← Category.assoc,
      SSet.Subcomplex.homOfLE_ι]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundaryFace_lift
    (show ULift.up.{u} (0 : Fin (n + 3)) < ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)
      from _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_pos n) p _ (finalHornFrontBoundaryFaceHom_compatible σ) g hj

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
