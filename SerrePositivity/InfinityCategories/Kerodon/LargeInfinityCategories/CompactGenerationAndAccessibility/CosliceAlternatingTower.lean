module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.CosliceAlternatingFactorization
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingStageExtension
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.RelativeAlternatingDiagram

/-!
概要：固定始域内で両成分の入力からの射を保持する全相対交互塔。
方針：同じ表示内の coslice 相対因子化を実際の一段延長へ渡す。
規約：底だけでなく固定始域内の全図式の整合を保持する。
使われ方：一般 accessible 引き戻しの小さい compact 成分対の生成。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：固定始域内の元の両表示を保持する全相対交互塔が存在する。
方針：同じ表示内の実際の相対因子化を全過去整合的な再帰へ渡す。
規約：余錐や延長の存在を追加入力として仮定しない。
使われ方：両成分入力からの全射を保持する長さ κ₀ の構成。 -/
lemma exists_relativeAlternatingTower_coslice_ind
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ)
    {A S : SSet.{u}} [Quasicategory A] [Quasicategory S]
    (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ S)
    (s₀ : (SSet.uliftFunctor.{u + 1, u}).obj S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity μ A)
    (hs₀ : ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (s₀.app (Opposite.op ⦋0⦌) v))
    {x : (Δ[0] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder s₀}
    {I : Fin 2 → SSet.{u}} [∀ c, Quasicategory (I c)] [∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ (I c)]
    {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x}
    (hP : ∀ c, ∀ v : (I c) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
      ((P c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection s₀).app (Opposite.op ⦋0⦌) (ULift.up v)))
    (hcol : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection s₀)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceDiagramCocone (P c))))
    : ∃ T : ∀ a, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.RelativeAlternatingClosedStage κ x I P a,
      ∀ a b, a < b → (T a).Restricts (T b) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_relativeAlternatingTower_of_extension
  intro a s
  obtain ⟨t⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_relativeAlternatingFactorization_coslice_ind
    h hS s₀ hs₀ hP hcol s (ofLex a).2
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_closedStage_of_relativeFactorization (ofLex a).1 (ofLex a).2 t

/-- 概要：固定始域内で両成分の全表示図式を保つ相対交互図式が存在する。
方針：実際の全相対塔を貼り合わせて元の成分表示への全制限を回収する。
規約：固定始域からの全高次成分も保持する。
使われ方：両成分の余極限比較と compact 成分対の生成。 -/
lemma exists_relativeAlternatingDiagram_coslice_ind
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ)
    {A S : SSet.{u}} [Quasicategory A] [Quasicategory S]
    (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ S)
    (s₀ : (SSet.uliftFunctor.{u + 1, u}).obj S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity μ A)
    (hs₀ : ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (s₀.app (Opposite.op ⦋0⦌) v))
    {x : (Δ[0] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder s₀}
    {I : Fin 2 → SSet.{u}} [∀ c, Quasicategory (I c)] [∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ (I c)]
    {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x}
    (hP : ∀ c, ∀ v : (I c) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
      ((P c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection s₀).app (Opposite.op ⦋0⦌) (ULift.up v)))
    (hcol : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection s₀)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceDiagramCocone (P c))))
    : ∃ F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x,
      ∃ J : ∀ c, nerve κ.ord.ToType ⟶ I c,
        ∀ c, (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingSection κ c)) ≫ F =
          (SSet.uliftFunctor.{u + 1, u}).map (J c) ≫ P c := by
  obtain ⟨T, hT⟩ := exists_relativeAlternatingTower_coslice_ind h hS s₀ hs₀ hP hcol
  obtain ⟨F, J, hc, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_relativeAlternatingDiagram_of_tower T hT
  exact ⟨F, J, hc⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
