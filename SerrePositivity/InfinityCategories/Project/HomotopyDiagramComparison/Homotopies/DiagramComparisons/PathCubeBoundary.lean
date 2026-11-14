module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.UpperMissingPath

/-!
概要：元の Path の全立方体境界と、trivial Kan 射に沿う境界固定の持ち上げ。
方針：内部点座標の全境界を取り、同じ包含と底の写像の可換正方形を持ち上げる。
規約：元の底の写像を保持。使われ方：外側ホーンの第二の未知 Hom の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra SSet

open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
open CategoryTheory.SimplicialThickening
variable {J : Type u} [LinearOrder J] {a b : J}

/-- 元の Path の内部点座標の全立方体境界。 -/
def pathCubeBoundary (hab : a < b) : (nerve (Path a b)).Subcomplex :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cubeBoundary (Set.Ioo a b)).preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathInteriorNerveIso hab).hom

/-- 同じ全境界への所属を、最後の欠けた内部点または最初の内部点で判定する。 -/
lemma mem_pathCubeBoundary_iff (hab : a < b) {n : SimplexCategoryᵒᵖ}
    (F : (nerve (Path a b)).obj n) :
    F ∈ (pathCubeBoundary hab).obj n ↔
      (∃ x : Set.Ioo a b, x.1 ∉ (F.obj (Fin.last n.unop.len)).I) ∨
        ∃ x : Set.Ioo a b, x.1 ∈ (F.obj 0).I := by
  change (∃ x : Set.Ioo a b, (∀ t, x.1 ∈ (F.obj t).I) ∨
    ∀ t, x.1 ∉ (F.obj t).I) ↔ _
  constructor
  · rintro ⟨x, h | h⟩
    · exact Or.inr ⟨x, h 0⟩
    · exact Or.inl ⟨x, h _⟩
  · rintro (⟨x, h⟩ | ⟨x, h⟩)
    · exact ⟨x, Or.inr (fun t ht ↦ h ((F.map (homOfLE (Fin.le_last t))).1.1.1 ht))⟩
    · exact ⟨x, Or.inl (fun t ↦ (F.map (homOfLE (Fin.zero_le t))).1.1.1 h)⟩

/-- 元の底の写像の上で、trivial Kan 射に沿って全境界を固定した持ち上げを取る。 -/
lemma pathCubeBoundary_lift (hab : a < b) {X Y : SSet.{u}} (p : X ⟶ Y)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] (f : (pathCubeBoundary hab : SSet) ⟶ X)
    (g : nerve (Path a b) ⟶ Y) (h : f ≫ p = (pathCubeBoundary hab).ι ≫ g) :
    ∃ l : nerve (Path a b) ⟶ X, (pathCubeBoundary hab).ι ≫ l = f ∧ l ≫ p = g := by
  have : HasLiftingProperty (pathCubeBoundary hab).ι p :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem _ inferInstance
  let sq : CommSq f (pathCubeBoundary hab).ι p g := ⟨h⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
