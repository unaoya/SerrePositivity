module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PathCubeBoundary
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HollowCover

/-!
# Path の全境界の座標面による貼り合わせ

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

variable {J : Type u} [LinearOrder J] {a b : J}

/-- Path の全境界の零座標面と合成面を同じ添字型で表す。 -/
def pathCubeBoundaryFace : Sum (Set.Ioo a b) (Set.Ioo a b) →
    (nerve (SimplicialThickening.Path a b)).Subcomplex :=
  Sum.elim (fun point ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids point.1) (fun point ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough point.1)

/-- 全零座標面と全合成面の和集合は元の Path の全境界に一致する。 -/
lemma iSup_pathCubeBoundaryFace (hab : a < b) :
    ⨆ j, pathCubeBoundaryFace (a := a) (b := b) j = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundary hab := by
  ext n F
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mem_pathCubeBoundary_iff]
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion]
  constructor
  · rintro ⟨j | j, hj⟩
    · exact Or.inl ⟨j, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.mem_pathAvoids_iff_last j.1 F).mp hj⟩
    · exact Or.inr ⟨j, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.mem_pathThrough_iff_first j.1 F).mp hj⟩
  · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
    · exact ⟨.inl j, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.mem_pathAvoids_iff_last j.1 F).mpr hj⟩
    · exact ⟨.inr j, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.mem_pathThrough_iff_first j.1 F).mpr hj⟩

/-- 全境界を、元の全ての座標面とその交わりによる余等化図式で被覆する。 -/
theorem pathCubeBoundaryCover (hab : a < b) :
    SSet.Subcomplex.MulticoequalizerDiagram (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundary hab) pathCubeBoundaryFace
      (fun j k ↦ pathCubeBoundaryFace j ⊓ pathCubeBoundaryFace k) where
  iSup_eq := iSup_pathCubeBoundaryFace hab
  eq_inf _ _ := rfl

/-- 各座標面を元の Path の全境界へ含める。 -/
lemma pathCubeBoundaryFace_le (hab : a < b) (j) :
    pathCubeBoundaryFace j ≤ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundary hab := by
  rw [← iSup_pathCubeBoundaryFace hab]
  exact le_iSup _ j

/-- 交わりで一致する全座標面の写像を元の全境界へ貼り合わせる。 -/
def pathCubeBoundaryGlue (hab : a < b) {X : SSet.{u}}
    (f : ∀ j, (pathCubeBoundaryFace (a := a) (b := b) j : SSet) ⟶ X)
    (hf : ∀ j k, SSet.Subcomplex.homOfLE
      (show pathCubeBoundaryFace j ⊓ pathCubeBoundaryFace k ≤ pathCubeBoundaryFace j
        from inf_le_left) ≫ f j = SSet.Subcomplex.homOfLE
      (show pathCubeBoundaryFace j ⊓ pathCubeBoundaryFace k ≤ pathCubeBoundaryFace k
        from inf_le_right) ≫ f k) : (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundary hab : SSet) ⟶ X :=
  Multicofork.IsColimit.desc (pathCubeBoundaryCover hab).isColimit f (fun ⟨j, k⟩ ↦ hf j k)

/-- 全境界の貼り合わせは指定した各面の写像を保持する。 -/
lemma pathCubeBoundaryGlue_on_face (hab : a < b) {X : SSet.{u}}
    (f : ∀ j, (pathCubeBoundaryFace (a := a) (b := b) j : SSet) ⟶ X)
    (hf : ∀ j k, SSet.Subcomplex.homOfLE
      (show pathCubeBoundaryFace j ⊓ pathCubeBoundaryFace k ≤ pathCubeBoundaryFace j
        from inf_le_left) ≫ f j = SSet.Subcomplex.homOfLE
      (show pathCubeBoundaryFace j ⊓ pathCubeBoundaryFace k ≤ pathCubeBoundaryFace k
        from inf_le_right) ≫ f k) (j) :
    SSet.Subcomplex.homOfLE (pathCubeBoundaryFace_le hab j) ≫ pathCubeBoundaryGlue hab f hf =
      f j :=
  Multicofork.IsColimit.fac (pathCubeBoundaryCover hab).isColimit f (fun ⟨j, k⟩ ↦ hf j k) j

/-- 全座標面を固定し、指定した底の写像を trivial Kan 射に沿って持ち上げる。 -/
lemma pathCubeBoundaryFace_lift (hab : a < b) {X Y : SSet.{u}} (p : X ⟶ Y)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p]
    (f : ∀ j, (pathCubeBoundaryFace (a := a) (b := b) j : SSet) ⟶ X)
    (hf : ∀ j k, SSet.Subcomplex.homOfLE
      (show pathCubeBoundaryFace j ⊓ pathCubeBoundaryFace k ≤ pathCubeBoundaryFace j
        from inf_le_left) ≫ f j = SSet.Subcomplex.homOfLE
      (show pathCubeBoundaryFace j ⊓ pathCubeBoundaryFace k ≤ pathCubeBoundaryFace k
        from inf_le_right) ≫ f k)
    (g : nerve (SimplicialThickening.Path a b) ⟶ Y)
    (hg : ∀ j, f j ≫ p = (pathCubeBoundaryFace j).ι ≫ g) :
    ∃ l : nerve (SimplicialThickening.Path a b) ⟶ X,
      (∀ j, (pathCubeBoundaryFace j).ι ≫ l = f j) ∧ l ≫ p = g := by
  have h : pathCubeBoundaryGlue hab f hf ≫ p = (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundary hab).ι ≫ g := by
    apply Multicofork.IsColimit.hom_ext (pathCubeBoundaryCover hab).isColimit
    intro j
    change SSet.Subcomplex.homOfLE (pathCubeBoundaryFace_le hab j) ≫
      (pathCubeBoundaryGlue hab f hf ≫ p) =
        SSet.Subcomplex.homOfLE (pathCubeBoundaryFace_le hab j) ≫
          ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundary hab).ι ≫ g)
    rw [← Category.assoc, pathCubeBoundaryGlue_on_face, hg, ← Category.assoc,
      SSet.Subcomplex.homOfLE_ι]
  obtain ⟨l, hl, hp⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundary_lift hab p (pathCubeBoundaryGlue hab f hf) g h
  refine ⟨l, ?_, hp⟩
  intro j
  rw [← SSet.Subcomplex.homOfLE_ι (pathCubeBoundaryFace_le hab j), Category.assoc, hl]
  exact pathCubeBoundaryGlue_on_face hab f hf j

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
