module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.SeededAlternatingTower

/-!
概要：固定小図式を保持する最終相対交互図式。
方針：入力の coslice 内で全塔を貼り合わせ、元の両表示内の成分図式を回収する。
規約：入力の全単体と両表示添字を保持する。
使われ方：元の入力図式を compact 成分対へ延長する全余極限構成。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：入力付き全相対塔は同じ入力の下の全交互図式に貼り合わさる。
方針：入力の coslice 内で全閉前置段を貼り、元の成分表示との等式を全被覆で判定する。
規約：入力の全単体を固定する。
使われ方：入力付きの両成分余極限比較。 -/
lemma exists_seededRelativeAlternatingDiagram_of_tower
    {κ : Cardinal.{u}} {K : SSet.{u}} {B : SSet.{u + 1}}
    {x : (Δ[0] : SSet.{u + 1}) ⟶ B} {I : Fin 2 → SSet.{u}}
    {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x}
    {z : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x}
    (T : ∀ a, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.SeededAlternatingClosedStage (κ := κ) (I := I) (P := P) z a)
    (hT : ∀ a b, a < b → (T a).Restricts (T b)) :
    ∃ R : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder z,
      ∃ J : ∀ c, nerve κ.ord.ToType ⟶ I c,
        ∀ c, (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingSection κ c)) ≫
          R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z = (SSet.uliftFunctor.{u + 1, u}).map (J c) ≫ P c := by
  obtain ⟨F, J, _, _, hJ⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_relativeAlternatingDiagram_of_tower
    (fun a ↦ (T a).stage) (fun a b h ↦ (hT a b h).1)
  have hle : ∀ a b (h : a ≤ b),
      (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.closedPrefixMap h)) ≫
        (T b).under = (T a).under := by
    intro a b h
    rcases h.lt_or_eq with h | rfl
    · exact (hT a b h).2 h.le
    · change (SSet.uliftFunctor.{u + 1, u}).map (𝟙 _) ≫ _ = _
      rw [(SSet.uliftFunctor.{u + 1, u}).map_id, Category.id_comp]
  obtain ⟨R, hR⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_closedPrefixGluing (fun a ↦ (T a).under) hle
  refine ⟨R, J, ?_⟩
  intro c
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.componentTower_ulift_hom_ext κ c
  intro a
  calc
    _ = (SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingClosedSection κ a c)) ≫
        (((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.closedPrefixInclusion a)) ≫ R) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z) := rfl
    _ = (SSet.uliftFunctor.{u + 1, u}).map ((T a).stage.index c) ≫ P c := by
      rw [hR a, (T a).projection, (T a).stage.component_eq c]
    _ = _ := by rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hJ a c]

/-- 概要：任意の小さい quasi 入力図式を保持する全相対交互図式が存在する。
方針：入力付きの実際の全相対塔を構成して貼り合わせる。
規約：元の全入力と両成分表示を保持し、入力図式の余極限は不要。
使われ方：一般 accessible 引き戻しの compact 成分対の生成。 -/
lemma exists_seededRelativeAlternatingDiagram
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ)
    {A K : SSet.{u}} [Quasicategory A] [Quasicategory K] (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ K)
    {x : (Δ[0] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity μ A}
    {I : Fin 2 → SSet.{u}} [∀ c, Quasicategory (I c)] [∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ (I c)]
    {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x}
    {z : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x}
    (hz : ∀ v : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
      ((z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x).app (Opposite.op ⦋0⦌) (ULift.up v)))
    (hP : ∀ c, ∀ v : (I c) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
      ((P c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x).app (Opposite.op ⦋0⦌) (ULift.up v)))
    (hcol : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceDiagramCocone (P c))) :
    ∃ R : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder z,
      ∃ J : ∀ c, nerve κ.ord.ToType ⟶ I c,
        ∀ c, (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingSection κ c)) ≫
          R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z = (SSet.uliftFunctor.{u + 1, u}).map (J c) ≫ P c := by
  obtain ⟨T, hT⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_seededRelativeAlternatingTower h hK hz hP hcol
  exact exists_seededRelativeAlternatingDiagram_of_tower T hT

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
