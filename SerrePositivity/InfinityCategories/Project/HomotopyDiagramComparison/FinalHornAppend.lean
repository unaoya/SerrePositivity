module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornLastPath

/-!
# 最終隣接 Path の付加と座標面

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

/-- 前半の native Path に最後の隣接 Path を付加する。 -/
def finalHornAppend (n : ℕ) :
    nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n))) ⟶
        nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
          (ULift.up (Fin.last (n + 2)))) :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFrontThroughIso n).hom ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n))).ι

/-- 最後の隣接 Path の付加は、各頂点の集合に最終頂点を加える操作である。 -/
lemma finalHornAppend_obj (n : ℕ) {m : SimplexCategoryᵒᵖ}
    (F : (nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)))).obj m) (t : Fin (m.unop.len + 1)) :
    (((finalHornAppend n).app m F).obj t).I =
      (F.obj t).I ∪ {ULift.up (Fin.last (n + 2))} := by
  ext x
  change (x ∈ (F.obj t).I ∨ x = ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) ∨
    x = ULift.up (Fin.last (n + 2)) ∨ _) ↔
      x ∈ (F.obj t).I ∨ x = ULift.up (Fin.last (n + 2))
  simp only [Set.mem_empty_iff_false, exists_false, or_false]
  constructor
  · rintro (h | rfl | h)
    · exact Or.inl h
    · exact Or.inl (F.obj t).right
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

/-- 最終頂点以外を避ける前半 Path は、最後の隣接 Path の付加後も同じ頂点を避ける。 -/
lemma finalHornAppend_avoids (n : ℕ) (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2))
    {m : SimplexCategoryᵒᵖ}
    (F : (nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)))).obj m)
    (hF : F ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up j)).obj m) :
    (finalHornAppend n).app m F ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up j)).obj m := by
  intro t h
  rw [finalHornAppend_obj] at h
  rcases h with h | h
  · exact hF t h
  · exact hj (congrArg ULift.down (Set.mem_singleton_iff.mp h))

/-- 前半の合成面は、最後の隣接 Path の付加によって同じ合成面へ写る。 -/
lemma finalHornAppend_through (n : ℕ) (b : Fin (n + 3))
    {m : SimplexCategoryᵒᵖ}
    (F : (nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)))).obj m)
    (hF : F ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b)).obj m) :
    (finalHornAppend n).app m F ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b)).obj m := by
  intro t
  rw [finalHornAppend_obj]
  exact Or.inl (hF t)

/-- 最後の隣接 Path の付加は、元の Path 合成の結合則と整合する。 -/
lemma finalHornAppend_comp (n : ℕ) (b : Fin (n + 3)) {m : SimplexCategoryᵒᵖ}
    (x : (nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up b))).obj m)
    (y : (nerve (SimplicialThickening.Path (ULift.up.{u} b)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)))).obj m) :
    (finalHornAppend n).app m ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up 0) (ULift.up b)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n))).app m (x, y)) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up 0) (ULift.up b) (ULift.up (Fin.last (n + 2)))).app m
      (x, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up b) (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n))
        (ULift.up (Fin.last (n + 2)))).app m
          (y, (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornLastPathIso n).hom.app m PUnit.unit)) := by
  exact CategoryTheory.Functor.ext (fun t ↦ by
    apply SimplicialThickening.Path.ext
    exact Set.union_assoc _ _ _)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
