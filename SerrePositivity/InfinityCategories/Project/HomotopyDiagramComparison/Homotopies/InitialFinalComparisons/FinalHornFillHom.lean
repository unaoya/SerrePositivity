module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.InitialFinalComparisons.FinalHornUnknownHom
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathDegeneracy

/-!
# 最終外側ホーンの全頂点対の Hom

概要：最終外側ホーンの二つの未知 Hom を、元の豊穣単体と相対充填へ組み立てる。
方針：全三対象の合成、全既知面への制限、薄い底の一意性を順に照合する。
規約：元の cf 置換と底射影を使い、内ホーンの欠損頂点条件を仮定しない。
使われ方：HTT 5.2.4.6 の元の右 Quillen 候補辺の Cartesian 性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory HomotopicalAlgebra MonoidalCategory SSet
open CategoryTheory.SimplicialThickening

open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {n : ℕ}
  (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ SimplicialNerve C)
  (g : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
    (ULift.up (Fin.last (n + 2)))) ⟶
      SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (Fin.last (n + 2))))
  (f : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
    (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n))) ⟶
      SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)))

/-- 未知区間は [0,penultimate] と [0,last] の二つに限られる。 -/
lemma finalHornUnknownInterval_endpoints (a b : Fin (n + 3))
    (h : ¬ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval a b) :
    a = 0 ∧ (b = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n ∨ b = Fin.last (n + 2)) := by
  have ha : a = 0 := not_not.mp (fun ha ↦ h (Or.inl ha))
  refine ⟨ha, ?_⟩
  have hb : ¬ b < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n := fun hb ↦ h (Or.inr hb)
  by_cases hbn : b = Fin.last (n + 2)
  · exact Or.inr hbn
  · left
    apply Fin.ext
    have hble : n + 1 ≤ b.val := not_lt.mp hb
    have hblt : b.val < n + 3 := b.isLt
    have hne : b.val ≠ n + 2 := fun h ↦ hbn (Fin.ext h)
    change b.val = n + 1
    omega

/-- 元の全頂点対に、既知区間の回収と二つの未知 Hom を組み合わせた Hom 写像を定義する。 -/
def finalHornFillHom (a b : Fin (n + 3)) :
    nerve (SimplicialThickening.Path (ULift.up.{u} a) (ULift.up b)) ⟶
      SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ a) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ b) :=
  if hab : a ≤ b then
    if hp : a ≠ 0 ∨ b < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n then
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom σ a b hab hp
    else by
      have he := finalHornUnknownInterval_endpoints a b hp
      obtain ⟨rfl, he⟩ := he
      by_cases hb : b = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n
      · subst b
        exact f
      · have hbl : b = Fin.last (n + 2) := he.resolve_left hb
        subst b
        exact g
  else _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathEmptyHom (ULift.up a) (ULift.up b) hab _

/-- 順序づけられた既知区間では、充填用 Hom は元の回収写像に一致する。 -/
lemma finalHornFillHom_known (a b : Fin (n + 3)) (hab : a ≤ b)
    (hp : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval a b) :
    finalHornFillHom σ g f a b = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom σ a b hab hp := by
  have hp' : a ≠ 0 ∨ b < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n := hp
  simp only [finalHornFillHom, dite_eq_left hab, dite_eq_left hp']

/-- 前半の未知区間には、元の全境界を固定して構成した Hom を用いる。 -/
lemma finalHornFillHom_front : finalHornFillHom σ g f 0 (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) = f := by
  simp only [finalHornFillHom, Fin.zero_le, dite_true,
    ne_self_iff_false, lt_self_iff_false, or_self, dite_false]

/-- 全区間には、元の空洞から延長した Hom を用いる。 -/
lemma finalHornFillHom_full : finalHornFillHom σ g f 0 (Fin.last (n + 2)) = g := by
  have hp : ¬ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval 0 (Fin.last (n + 2)) := by
    rintro (h | h)
    · exact h rfl
    · exact (not_lt_of_ge (le_of_lt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n))) h
  have hnp : Fin.last (n + 2) ≠ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n :=
    ne_of_gt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n)
  have hp' : ¬ ((0 : Fin (n + 3)) ≠ 0 ∨ Fin.last (n + 2) < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) := hp
  simp only [finalHornFillHom, Fin.zero_le, dite_true, dite_eq_right hp', dite_eq_right hnp]

/-- 全頂点対の充填用 Hom は、元の豊穣単位を保存する。 -/
lemma finalHornFillHom_id (a : Fin (n + 3)) :
    eId SSet (SimplicialThickening.mk (ULift.up.{u} a)) ≫ finalHornFillHom σ g f a a =
      eId SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ a) := by
  have hp : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval a a := by
    by_cases ha : a = 0
    · right
      simpa only [ha] using _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_pos n
    · exact Or.inl ha
  rw [finalHornFillHom_known σ g f a a le_rfl hp]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom_id σ a hp

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
