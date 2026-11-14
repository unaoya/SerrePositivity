module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.UpperMissingPath
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HollowCover

/-!
概要：上面を一つ欠く Path の部分単体集合を、元の零座標面と合成面で被覆する。
方針：最初・最後の頂点で所属を判定し、部分単体集合の余極限で貼り合わせる。
規約：面の整合性は入力。ホーンからこの整合性を導く証明は別途必要。
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

/-- 全零座標面と、指定面を除く合成面を一つの族にする。 -/
def upperMissingPathFace (i : Set.Ioo a b) :
    Sum (Set.Ioo a b) {j : Set.Ioo a b // j ≠ i} → (nerve (Path a b)).Subcomplex :=
  Sum.elim (fun point ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids point.1) (fun point ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough point.1.1)

/-- 面族の和は、指定合成面一つを欠く既知部分そのもの。 -/
lemma iSup_upperMissingPathFace (hab : a < b) (i : Set.Ioo a b) :
    ⨆ j, upperMissingPathFace i j = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingPath hab i := by
  ext n F
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mem_upperMissingPath_iff]
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion]
  constructor
  · rintro ⟨j | j, hj⟩
    · exact Or.inl ⟨j, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.mem_pathAvoids_iff_last j.1 F).mp hj⟩
    · exact Or.inr ⟨j.1, j.2, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.mem_pathThrough_iff_first j.1.1 F).mp hj⟩
  · rintro (⟨j, hj⟩ | ⟨j, hji, hj⟩)
    · exact ⟨.inl j, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.mem_pathAvoids_iff_last j.1 F).mpr hj⟩
    · exact ⟨.inr ⟨j, hji⟩, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.mem_pathThrough_iff_first j.1 F).mpr hj⟩

/-- 同じ面族と二面の交わりによる、既知部分の正確な多重余等化子表示。 -/
theorem upperMissingPathCover (hab : a < b) (i : Set.Ioo a b) :
    SSet.Subcomplex.MulticoequalizerDiagram (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingPath hab i) (upperMissingPathFace i)
      (fun j k ↦ upperMissingPathFace i j ⊓ upperMissingPathFace i k) where
  iSup_eq := iSup_upperMissingPathFace hab i
  eq_inf _ _ := rfl

/-- 同じ各面を、指定合成面一つを欠く既知部分へ含める。 -/
lemma upperMissingPathFace_le (hab : a < b) (i : Set.Ioo a b)
    (j : Sum (Set.Ioo a b) {j : Set.Ioo a b // j ≠ i}) :
    upperMissingPathFace i j ≤ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingPath hab i := by
  rw [← iSup_upperMissingPathFace hab i]
  exact le_iSup _ j

/-- 二面の交わりで一致する入力写像を、同じ既知部分へ貼り合わせる。 -/
def upperMissingPathGlue (hab : a < b) (i : Set.Ioo a b) {X : SSet.{u}}
    (f : ∀ j, (upperMissingPathFace i j : SSet) ⟶ X)
    (hf : ∀ j k, SSet.Subcomplex.homOfLE
      (show upperMissingPathFace i j ⊓ upperMissingPathFace i k ≤ upperMissingPathFace i j
        from inf_le_left) ≫ f j = SSet.Subcomplex.homOfLE
      (show upperMissingPathFace i j ⊓ upperMissingPathFace i k ≤ upperMissingPathFace i k
        from inf_le_right) ≫ f k) : (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingPath hab i : SSet) ⟶ X :=
  Multicofork.IsColimit.desc (upperMissingPathCover hab i).isColimit f
    (fun ⟨j, k⟩ ↦ hf j k)

/-- 貼り合わせを各元の面へ戻すと、元の入力写像に一致する。 -/
lemma upperMissingPathGlue_on_face (hab : a < b) (i : Set.Ioo a b) {X : SSet.{u}}
    (f : ∀ j, (upperMissingPathFace i j : SSet) ⟶ X)
    (hf : ∀ j k, SSet.Subcomplex.homOfLE
      (show upperMissingPathFace i j ⊓ upperMissingPathFace i k ≤ upperMissingPathFace i j
        from inf_le_left) ≫ f j = SSet.Subcomplex.homOfLE
      (show upperMissingPathFace i j ⊓ upperMissingPathFace i k ≤ upperMissingPathFace i k
        from inf_le_right) ≫ f k)
    (j : Sum (Set.Ioo a b) {j : Set.Ioo a b // j ≠ i}) :
    SSet.Subcomplex.homOfLE (upperMissingPathFace_le hab i j) ≫
      upperMissingPathGlue hab i f hf = f j :=
  Multicofork.IsColimit.fac (upperMissingPathCover hab i).isColimit f (fun ⟨j, k⟩ ↦ hf j k) j

/-- 整合する面写像を Kan 複体内の元の全 Path Hom へ延長し、全既知面を保持する。 -/
lemma upperMissingPathFace_extension (hab : a < b) (i : Set.Ioo a b)
    {X : SSet.{u}} [KanComplex X]
    (f : ∀ j, (upperMissingPathFace i j : SSet) ⟶ X)
    (hf : ∀ j k, SSet.Subcomplex.homOfLE
      (show upperMissingPathFace i j ⊓ upperMissingPathFace i k ≤ upperMissingPathFace i j
        from inf_le_left) ≫ f j = SSet.Subcomplex.homOfLE
      (show upperMissingPathFace i j ⊓ upperMissingPathFace i k ≤ upperMissingPathFace i k
        from inf_le_right) ≫ f k) :
    ∃ g : nerve (Path a b) ⟶ X, ∀ j, (upperMissingPathFace i j).ι ≫ g = f j := by
  obtain ⟨g, hg⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingPath_extension hab i (upperMissingPathGlue hab i f hf)
  refine ⟨g, fun j ↦ ?_⟩
  rw [← SSet.Subcomplex.homOfLE_ι (upperMissingPathFace_le hab i j), Category.assoc, hg]
  exact upperMissingPathGlue_on_face hab i f hf j

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
