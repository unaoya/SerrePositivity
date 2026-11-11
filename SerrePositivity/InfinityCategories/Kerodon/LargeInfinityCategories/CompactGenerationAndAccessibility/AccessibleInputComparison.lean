module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IndInputReflection

/-!
概要：元の accessible な底で入力付き compact 成分対と全比較同型を構成する。
方針：元の底の共通 Ind 解像で交互構成し、固定入力上の比較を元の底へ反映する。
規約：元の全入力と標的を保持し、Ind 表示を追加入力にしない。
使われ方：元の厳密引き戻し内の compact 成分対の生成。

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

/-- 概要：元の accessible な底で入力と標的を保つ compact 成分対の像は同型になる。
方針：実際の Ind 解像で同じ相対交互構成を行い、全入力付き同型を元の底へ戻す。
規約：元の底の同値表現や比較の存在を追加仮定にしない。
使われ方：EquivalenceLifting による元の引き戻し内の厳密化。 -/
lemma exists_compactInputColimitComparison_of_isKappaAccessible_base
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ)
    {K : SSet.{u}} [Quasicategory K] (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ K)
    {B : SSet.{u + 1}} [Quasicategory B] (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ B)
    (C : Fin 2 → SSet.{u + 1}) [∀ c, Quasicategory (C c)]
    (hC : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ (C c))
    (hCκ : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ (C c))
    (hBκ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ (B))
    (p : ∀ c, C c ⟶ B)
    (hp : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (p c))
    (hpκ : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (p c))
    (hpCompact : ∀ c, ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ v →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ ((p c).app (Opposite.op ⦋0⦌) v))
    (q : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C c)
    (hqCompact : ∀ c, ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
      ((q c).app (Opposite.op ⦋0⦌) v))
    (r : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ B)
    (hq : ∀ c, q c ≫ p c = r)
    (z : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (q c)) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r)
    (hz : ∀ c, (z c).val ≫ p c = t.val) :
    ∃ v : ∀ c, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (q c))).symm (z c))) _⦋0⦌,
      (∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (q c))).symm (z c)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (q c)).app (Opposite.op ⦋0⦌) (v c))) ∧
      (∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (q c))).symm (z c)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (q c) ≫ p c).app (Opposite.op ⦋0⦌) (v c))) ∧
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputPostcomp (q 0) (p 0) r (hq 0) (z 0) t (hz 0)).app (Opposite.op ⦋0⦌) (v 0))
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputPostcomp (q 1) (p 1) r (hq 1) (z 1) t (hz 1)).app (Opposite.op ⦋0⦌) (v 1))) := by
  obtain ⟨R⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.nonempty_indBaseResolution_of_isKappaAccessible hB
  let β := R.comparison
  have heβ := R.comparison_isQCatEquivalence
  let p' := fun c ↦ p c ≫ β
  have hp' : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (p' c) := fun c ↦
    (hp c).comp (_root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.equivalence_preservesSmallKappaFilteredColimits μ heβ)
  have hpκ' : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (p' c) := fun c ↦
    (hpκ c).comp (_root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.equivalence_preservesSmallKappaFilteredColimits κ heβ)
  have hcompact : ∀ c, ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ v →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ ((p' c).app (Opposite.op ⦋0⦌) v) := by
    intro c v hv
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaCompact_image_of_equivalence heβ.choose
      ((p c).app (Opposite.op ⦋0⦌) v) (hpCompact c v hv)
  have hq' : ∀ c, q c ≫ p' c = r ≫ β := by
    intro c
    dsimp only [p']
    rw [← Category.assoc, hq c]
  have hz' : ∀ c, (z c).val ≫ p' c = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone β t).val := by
    intro c
    change (z c).val ≫ (p c ≫ β) = t.val ≫ β
    rw [← Category.assoc, hz c]
  obtain ⟨v, hc, _, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_compactInputColimitComparison h hK C hC hCκ
    (R.model_hasSmallKappaFilteredColimits hBκ) p' hp' hpκ' hcompact q hqCompact
    (r ≫ β) hq' z (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone β t) hz'
  let W := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputPostcomp r β (r ≫ β) rfl t (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone β t) rfl
  let T := fun c ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputPostcomp (q c) (p c) r (hq c) (z c) t (hz c)
  have hcomp (c : Fin 2) : T c ≫ W =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputPostcomp (q c) (p' c) (r ≫ β) (hq' c) (z c) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone β t) (hz' c) := by
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputPostcomp_comp (q c) (p c) r (hq c) β (r ≫ β) rfl
      (z c) t (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone β t) (hz c) rfl
  have he' : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      (W.app (Opposite.op ⦋0⦌) ((T 0).app (Opposite.op ⦋0⦌) (v 0)))
      (W.app (Opposite.op ⦋0⦌) ((T 1).app (Opposite.op ⦋0⦌) (v 1)))) := by
    obtain ⟨he⟩ := he
    refine ⟨?_⟩
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((T 0 ≫ W).app (Opposite.op ⦋0⦌) (v 0))
      ((T 1 ≫ W).app (Opposite.op ⦋0⦌) (v 1))
    rw [hcomp 0, hcomp 1]
    exact he
  have hback := R.nonempty_inputVertexIso_of_comparison r t he'
  refine ⟨v, hc, ?_, hback⟩
  intro c
  exact hpCompact c _ (hc c)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
