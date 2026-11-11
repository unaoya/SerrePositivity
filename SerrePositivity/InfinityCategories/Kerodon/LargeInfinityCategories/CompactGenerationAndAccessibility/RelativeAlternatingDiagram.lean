module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.ComponentTowerGluing

/-!
概要：元の両表示内に値を取る最終相対交互図式を全塔から構成する。
方針：全閉前置図式と両成分表示を貼り合わせ、各成分の等式を全単体被覆で示す。
規約：同じ固定対象上の全 slice 図式を使用する。
使われ方：両成分の κ₀-filtered 余極限と compact 成分対の構成。

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

/-- 概要：整合した全相対塔は元の両表示内の全交互図式へ貼り合わさる。
方針：全図式と両表示を厳密に貼り合わせ、全閉成分段上で成分条件を比較する。
規約：塔の全閉前置制限も同時に返す。
使われ方：最終図式の両成分の余極限比較。 -/
lemma exists_relativeAlternatingDiagram_of_tower
    {κ : Cardinal.{u}} {B : SSet.{u + 1}}
    {x : (Δ[0] : SSet.{u + 1}) ⟶ B} {I : Fin 2 → SSet.{u}}
    {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x}
    (T : ∀ a, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.RelativeAlternatingClosedStage κ x I P a)
    (hT : ∀ a b, a < b → (T a).Restricts (T b)) :
    ∃ F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x,
      ∃ J : ∀ c, nerve κ.ord.ToType ⟶ I c,
        (∀ c, (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingSection κ c)) ≫ F =
          (SSet.uliftFunctor.{u + 1, u}).map (J c) ≫ P c) ∧
        (∀ a, (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.closedPrefixInclusion a)) ≫
          F = (T a).diagram) ∧
        ∀ a c, nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.componentClosedInclusion κ a c) ≫ J c = (T a).index c := by
  have hle : ∀ a b, a ≤ b → (T a).Restricts (T b) := by
    intro a b h
    rcases h.lt_or_eq with h | rfl
    · exact hT a b h
    · intro h
      constructor
      · change (SSet.uliftFunctor.{u + 1, u}).map (𝟙 _) ≫ _ = _
        rw [(SSet.uliftFunctor.{u + 1, u}).map_id, Category.id_comp]
      · intro c
        change (𝟙 _) ≫ _ = _
        exact Category.id_comp _
  obtain ⟨F, hF⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_closedPrefixGluing (fun a ↦ (T a).diagram)
    (fun a b h ↦ (hle a b h h).1)
  have hj (c : Fin 2) : ∃ J : nerve κ.ord.ToType ⟶ I c,
      ∀ a, nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.componentClosedInclusion κ a c) ≫ J = (T a).index c :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_componentTowerGluing κ c (fun a ↦ (T a).index c)
      (fun a b h ↦ (hle a b h h).2 c)
  choose J hJ using hj
  refine ⟨F, J, ?_, hF, fun a c ↦ hJ c a⟩
  intro c
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.componentTower_ulift_hom_ext κ c
  intro a
  calc
    _ = (SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingClosedSection κ a c)) ≫
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.closedPrefixInclusion a)) ≫ F) := rfl
    _ = (SSet.uliftFunctor.{u + 1, u}).map ((T a).index c) ≫ P c := by
      rw [hF a, (T a).component_eq c]
    _ = _ := by
      rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hJ c a]

/-- 概要：元の両表示を固定する全相対交互図式が存在する。
方針：実際に構成した全相対塔を貼り合わせる。
規約：元の表示添字と固定対象上の全図式を保持する。
使われ方：一般 accessible 引き戻しの compact 成分対の生成。 -/
lemma exists_relativeAlternatingDiagram
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ)
    {A : SSet.{u}} [Quasicategory A]
    {x : (Δ[0] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity μ A}
    {I : Fin 2 → SSet.{u}} [∀ c, Quasicategory (I c)] [∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ (I c)]
    {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x}
    (hP : ∀ c, ∀ v : (I c) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
      ((P c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x).app (Opposite.op ⦋0⦌) (ULift.up v)))
    (hcol : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceDiagramCocone (P c))) :
    ∃ F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x,
      ∃ J : ∀ c, nerve κ.ord.ToType ⟶ I c,
        ∀ c, (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingSection κ c)) ≫ F =
          (SSet.uliftFunctor.{u + 1, u}).map (J c) ≫ P c := by
  obtain ⟨T, hT⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_relativeAlternatingTower h hP hcol
  obtain ⟨F, J, h, _⟩ := exists_relativeAlternatingDiagram_of_tower T hT
  exact ⟨F, J, h⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
