module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.SeededAlternatingExtension

/-!
概要：固定小図式を保持する長さ κ₀ の全相対交互塔。
方針：実際の入力付き余錐から全過去段への延長を作り well-founded 選択を使う。
規約：入力付き延長の存在を追加仮定にしない。
使われ方：compact 成分対の comma の生成性と filtered 性。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：入力付き一段延長は入力付き厳密前置段で保持した全過去段も保持する。
方針：元の二つの前置包含を合成する。
規約：元の全入力と両成分添字の等式を保持する。
使われ方：well-founded 選択に渡す全過去整合。 -/
lemma SeededAlternatingClosedStage.restricts_of_extendsOpen
    {κ : Cardinal.{u}} {K : SSet.{u}} {B : SSet.{u + 1}}
    {x : (Δ[0] : SSet.{u + 1}) ⟶ B} {I : Fin 2 → SSet.{u}}
    {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x}
    {z : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x} {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ}
    {r : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.SeededAlternatingClosedStage (κ := κ) (I := I) (P := P) z a}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.SeededAlternatingOpenStage (κ := κ) (I := I) (P := P) z a}
    {t : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.SeededAlternatingClosedStage (κ := κ) (I := I) (P := P) z b}
    (hb : b < a) (hrs : r.ExtendsOpen s) (hst : s.Preserves hb t) : t.Restricts r := by
  refine ⟨r.stage.restricts_of_extendsOpen hb hrs.1 hst.1, ?_⟩
  intro h
  calc
    _ = (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.closedPrefixIntoStrict a ⟨b, hb⟩)) ≫
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.strictPrefixToClosed a)) ≫ r.under) := rfl
    _ = _ := by rw [hrs.2]; exact hst.2

/-- 概要：固定小図式を伴う全過去整合的な相対交互塔が存在する。
方針：入力付き全前置図式を同じ成分表示内へ因子化し、実際の一段延長を選択する。
規約：元の入力図式の余極限や新たな一般分類を仮定しない。
使われ方：任意の小さい入力図式を compact 成分対へ延長する。 -/
lemma exists_seededRelativeAlternatingTower
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
    ∃ T : ∀ a, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.SeededAlternatingClosedStage (κ := κ) (I := I) (P := P) z a,
      ∀ a b, a < b → (T a).Restricts (T b) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_wellFounded_coherentChoice (I := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ) wellFounded_lt
    (fun a ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.SeededAlternatingClosedStage (κ := κ) (I := I) (P := P) z a)
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.SeededAlternatingClosedStage.Restricts
  intro a prev hprev
  let f := fun b : {i : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ // i < a} ↦ prev b.val b.property
  have hf : ∀ b d : {i : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ // i < a}, b < d → (f b).Restricts (f d) := by
    intro b d hbd
    exact hprev b.val d.val b.property d.property hbd
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_seededAlternatingOpenStage_preserving a f hf
  obtain ⟨j, d, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_seededAlternatingCocone h hK hz hP hcol s (ofLex a).2
  obtain ⟨r, hr⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_seededClosedStage_of_cocone (ofLex a).1 (ofLex a).2 j d hc
  exact ⟨r, fun b hb ↦ r.restricts_of_extendsOpen hb hr (hs ⟨b, hb⟩)⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
