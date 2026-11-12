module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornIntervalHom
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionRecovery

/-!
概要：最終外側ホーンの二つの既知区間から、元の合成面の Hom 写像を回収する。
方針：元の Path 合成面の分割同型と回収した二つの Hom の合成を使う。
規約：penultimate の未知合成面は除く。使われ方：上面一つを欠く空洞の構成。
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

/-- 二つの既知 Hom を元の合成で結び、同じ合成面上の写像を作る。 -/
def finalHornCompositionHom (a b c : Fin (n + 3)) (hab : a ≤ b) (hbc : b ≤ c)
    (hpab : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval a b) (hpbc : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval b c) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := ULift.up.{u} a) (c := ULift.up c) (ULift.up b) : SSet) ⟶
      SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ a) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ c) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughIso (ULift.up a) (ULift.up b) (ULift.up c)).inv ≫
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom σ a b hab hpab ⊗ₘ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom σ b c hbc hpbc) ≫
      SimplicialCategory.sHomComp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ a) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ b) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ c)

/-- 同じ合成面を分割すると、回収した二つの元の Hom の合成に戻る。 -/
lemma finalHornCompositionHom_on_product (a b c : Fin (n + 3)) (hab : a ≤ b) (hbc : b ≤ c)
    (hpab : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval a b) (hpbc : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval b c) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughIso (ULift.up.{u} a) (ULift.up b) (ULift.up c)).hom ≫
      finalHornCompositionHom σ a b c hab hbc hpab hpbc =
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom σ a b hab hpab ⊗ₘ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom σ b c hbc hpbc) ≫
      SimplicialCategory.sHomComp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ a) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ b) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ c) := by
  simp [finalHornCompositionHom]

/-- 外側区間も既知なら、合成面写像は同じ既知 Hom 回収の制限に一致。 -/
lemma finalHornCompositionHom_eq_known (a b c : Fin (n + 3)) (hab : a ≤ b) (hbc : b ≤ c)
    (hpab : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval a b) (hpbc : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval b c)
    (hpac : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval a c) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := ULift.up.{u} a) (c := ULift.up c) (ULift.up b)).ι ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom σ a c (hab.trans hbc) hpac =
        finalHornCompositionHom σ a b c hab hbc hpab hpbc := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughIso (ULift.up.{u} a) (ULift.up b) (ULift.up c)).hom).mp
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughIso_hom_ι]
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom σ a b hab hpab ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom σ b c hbc hpbc) ≫
          SimplicialCategory.sHomComp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ a) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ b) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ c) :=
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom_comp σ a b c hab hbc hpab hpbc hpac
    _ = _ := by simp [finalHornCompositionHom]

/-- penultimate より前の切断点で、全区間の元の合成面写像を回収する。 -/
def finalHornUpperCompositionHom (b : Fin (n + 3))
    (hb0 : 0 < b) (hbp : b < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := ULift.up.{u} (0 : Fin (n + 3)))
      (c := ULift.up (Fin.last (n + 2))) (ULift.up b) : SSet) ⟶
      SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (Fin.last (n + 2))) :=
  finalHornCompositionHom σ 0 b (Fin.last (n + 2)) (Fin.zero_le b) (Fin.le_last b)
    (Or.inr hbp) (Or.inl (ne_of_gt hb0))

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
