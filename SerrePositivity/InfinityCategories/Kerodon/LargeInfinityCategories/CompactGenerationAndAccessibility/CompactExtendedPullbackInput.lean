module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.ExtendedInputVertexData

/-!
概要：accessible な二成分族から追加入力を保つ元の compact 引き戻し頂点を作る。
方針：同じ二成分族の表示内で交互構成し、第一脚で全入力付き像を厳密化する。
規約：元の全入力と標的を保ち、二成分の型を途中で取り替えない。
使われ方：compact 成分射影の指定始点の下の全試験。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：元の accessible 成分族から追加入力を保つ compact な引き戻し頂点を作る。
方針：同じ成分族の表示内の相対交互構成を元の第一脚で厳密化して貼る。
規約：元の全入力と標的、制限前の二つの成分頂点を保持する。
使われ方：指定成分始点を保つ under comma の全余錐。 -/
lemma exists_compactExtendedInputPullbackVertex_family
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ)
    {K : SSet.{u}} [Quasicategory K] (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ K)
    {B : SSet.{u + 1}} [Quasicategory B] (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ B)
    (C : Fin 2 → SSet.{u + 1}) [∀ c, Quasicategory (C c)]
    (L : Fin 2 → SSet.{u}) [∀ c, Quasicategory (L c)]
    (hL : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ (L c)) (hC : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ (C c))
    (hCκ : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ (C c))
    (hBκ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ B)
    (p : ∀ c, C c ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting (p 0))
    (hpμ : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (p c))
    (hpκ : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (p c))
    (hpCompact : ∀ c, ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ v →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ ((p c).app (Opposite.op ⦋0⦌) v))
    (a : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ pullback (p 0) (p 1)) (z : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone a)
    (q : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (L c) ⟶ C c)
    (hqCompact : ∀ c, ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
      ((q c).app (Opposite.op ⦋0⦌) v))
    (i : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj K ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (L c)) [Mono (i 0)]
    (hi : ∀ c, i c ≫ q c = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.pullbackComponentInput p a c)
    (zc : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (q c))
    (hzi : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (i c) (𝟙 Δ[0]) ≫ (zc c).val = (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.pullbackComponentInputCocone p a z c).val) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.ExtendedInputPullbackVertexData μ p a z q i hi zc hzi) := by
  let a₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.pullbackComponentInput p a
  let z₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.pullbackComponentInputCocone p a z
  let r := (a ≫ pullback.fst (p 0) (p 1)) ≫ p 0
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (p 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (pullback.fst (p 0) (p 1)) z)
  have hQ : (a ≫ pullback.snd (p 0) (p 1)) ≫ p 1 = r := by
    simp only [r, Category.assoc, pullback.condition]
  have hZ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (pullback.snd (p 0) (p 1)) z).val ≫ p 1 = t.val := by
    change (z.val ≫ pullback.snd (p 0) (p 1)) ≫ p 1 =
      (z.val ≫ pullback.fst (p 0) (p 1)) ≫ p 0
    simp only [Category.assoc, pullback.condition]
  have hpr : ∀ c, a₀ c ≫ p c = r := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.finitePairSection _ rfl hQ
  have hzt : ∀ c, (z₀ c).val ≫ p c = t.val := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.finitePairSection _ rfl hZ
  obtain ⟨v, hc, ⟨he⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_extendedInputComparison_of_accessible_components h hK hB
    C L hL hC hCκ hBκ p hpμ hpκ hpCompact q hqCompact a₀ i hi zc z₀ hzi r hpr t hzt
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.nonempty_extendedInputPullbackVertexData_of_compatible μ p a z q i hi zc hzi
    hp hpr hzt v hc he

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
