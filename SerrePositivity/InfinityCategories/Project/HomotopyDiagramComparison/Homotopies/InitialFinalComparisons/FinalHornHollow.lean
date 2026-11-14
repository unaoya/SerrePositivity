module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.InitialFinalComparisons.FinalHornFaceCompatibility
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.UpperMissingPathCover

/-!
概要：実際の最終外側ホーンから、上面一つを欠く Path の Hom 写像を貼り合わせる。
方針：回収した全零座標面・既知合成面と証明済みの整合性を使い、Kan 延長する。
規約：未知 Hom は二区間。豊穣単体全体の復元は別途必要。使われ方：γ4 の第一段階。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory SSet
open CategoryTheory.SimplicialThickening

open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {n : ℕ}
  (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ SimplicialNerve C)

/-- 最終外側ホーンの全区間で、未知合成面に対応する penultimate 内部点。 -/
def finalHornHollowPoint (n : ℕ) :
    Set.Ioo (ULift.up.{u} (0 : Fin (n + 3))) (ULift.up (Fin.last (n + 2))) :=
  ⟨ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n), _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_pos n, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n⟩

/-- 未知合成面と異なる内部点は penultimate より前にある。 -/
lemma finalHornHollowOtherPoint_lt
    (j : {j : Set.Ioo (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (Fin.last (n + 2))) // j ≠ finalHornHollowPoint n}) :
    j.1.1.down < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.lt_finalHornPenultimate_of_lt_last_ne j.1.1.down j.1.2.2
    (fun h ↦ j.2 (Subtype.ext (ULift.ext h)))

/-- 実際の最終外側ホーンから、全零座標面と既知合成面の Hom 写像を回収する。 -/
def finalHornHollowFaceHom :
    ∀ j, (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingPathFace (finalHornHollowPoint.{u} n) j : SSet) ⟶
      SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (Fin.last (n + 2))) := by
  intro j
  rcases j with j | j
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornInnerZeroHom σ j.1.down (ne_of_lt j.2.2) j.2.1 j.2.2
  · exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornUpperCompositionHom σ j.1.1.down j.1.2.1 (finalHornHollowOtherPoint_lt j)

/-- 回収した全ての既知面の写像は、二面の交わりで厳密に一致する。 -/
lemma finalHornHollowFaceHom_compatible :
    ∀ j k, SSet.Subcomplex.homOfLE
      (show _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingPathFace (finalHornHollowPoint.{u} n) j ⊓
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingPathFace (finalHornHollowPoint n) k ≤
          _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingPathFace (finalHornHollowPoint n) j from inf_le_left) ≫
        finalHornHollowFaceHom σ j = SSet.Subcomplex.homOfLE
      (show _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingPathFace (finalHornHollowPoint.{u} n) j ⊓
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingPathFace (finalHornHollowPoint n) k ≤
          _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingPathFace (finalHornHollowPoint n) k from inf_le_right) ≫
        finalHornHollowFaceHom σ k := by
  rintro (j | j) (k | k)
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornInnerZeroHom_overlap σ j.1.down k.1.down (ne_of_lt j.2.2)
      (ne_of_lt k.2.2) j.2.1 j.2.2 k.2.1 k.2.2
  · exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornZeroHom_composition_overlap σ j.1.down k.1.1.down
      j.2.1 j.2.2 k.1.2.1 (finalHornHollowOtherPoint_lt k)
  · have he := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornZeroHom_composition_overlap σ k.1.down j.1.1.down
      k.2.1 k.2.2 j.1.2.1 (finalHornHollowOtherPoint_lt j)
    apply CategoryTheory.NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro F
    exact (congrArg (fun f ↦ f.app m ⟨F.1, ⟨F.2.2, F.2.1⟩⟩) he).symm
  · exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornUpperCompositionHom_overlap σ j.1.1.down k.1.1.down
      j.1.2.1 (finalHornHollowOtherPoint_lt j) k.1.2.1 (finalHornHollowOtherPoint_lt k)

/-- 実際の最終外側ホーンから、同じ上面欠損 Path の Hom 写像を貼り合わせる。 -/
def finalHornHollowHom :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingPath
      (show ULift.up.{u} (0 : Fin (n + 3)) < ULift.up (Fin.last (n + 2))
        from (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_pos n).trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n))
      (finalHornHollowPoint n) : SSet) ⟶
        SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (Fin.last (n + 2))) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingPathGlue _ _ (finalHornHollowFaceHom σ) (finalHornHollowFaceHom_compatible σ)

/-- 貼り合わせを各既知面へ戻すと、同じホーンから回収した写像に一致する。 -/
lemma finalHornHollowHom_on_face (j) :
    SSet.Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingPathFace_le
      (show ULift.up.{u} (0 : Fin (n + 3)) < ULift.up (Fin.last (n + 2))
        from (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_pos n).trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n))
      (finalHornHollowPoint n) j) ≫ finalHornHollowHom σ = finalHornHollowFaceHom σ j :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingPathGlue_on_face _ _ _ _ j

/-- 端点 Hom が Kan なら、全既知面を固定して同じ全区間の Path Hom へ延長する。 -/
lemma finalHornHollowHom_extension
    [KanComplex (SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (Fin.last (n + 2))))] :
    ∃ g : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (Fin.last (n + 2)))) ⟶
        SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (Fin.last (n + 2))),
      ∀ j, (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingPathFace (finalHornHollowPoint n) j).ι ≫ g =
        finalHornHollowFaceHom σ j :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingPathFace_extension
    (show ULift.up.{u} (0 : Fin (n + 3)) < ULift.up (Fin.last (n + 2))
      from (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_pos n).trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n))
    (finalHornHollowPoint n) (finalHornHollowFaceHom σ) (finalHornHollowFaceHom_compatible σ)

/-- 同じ延長は全零座標面と penultimate 以外の全合成面の写像を保持する。 -/
lemma finalHornHollowHom_extension_components
    [KanComplex (SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (Fin.last (n + 2))))] :
    ∃ g : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (Fin.last (n + 2)))) ⟶
        SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (Fin.last (n + 2))),
      (∀ (j : Fin (n + 3)) (hj0 : 0 < j) (hjn : j < Fin.last (n + 2)),
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up j)).ι ≫ g = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornInnerZeroHom σ j (ne_of_lt hjn) hj0 hjn) ∧
      ∀ (b : Fin (n + 3)) (hb0 : 0 < b) (hbp : b < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n),
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b)).ι ≫ g = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornUpperCompositionHom σ b hb0 hbp := by
  obtain ⟨g, hg⟩ := finalHornHollowHom_extension σ
  refine ⟨g, ?_, ?_⟩
  · intro j hj0 hjn
    exact hg (.inl ⟨ULift.up j, hj0, hjn⟩)
  · intro b hb0 hbp
    let q : Set.Ioo (ULift.up.{u} (0 : Fin (n + 3))) (ULift.up (Fin.last (n + 2))) :=
      ⟨ULift.up b, hb0, hbp.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n)⟩
    have hq : q ≠ finalHornHollowPoint n := by
      intro h
      exact (ne_of_lt hbp) (congrArg (fun z ↦ z.val.down) h)
    exact hg (.inr ⟨q, hq⟩)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
