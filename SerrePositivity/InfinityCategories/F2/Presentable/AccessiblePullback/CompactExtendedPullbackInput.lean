module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.ExtendedInputVertexData

/-!
概要：accessible な二成分族から追加入力を保つ元の compact 引き戻し頂点を作る。
方針：同じ二成分族の表示内で交互構成し、第一脚で全入力付き像を厳密化する。
規約：元の全入力と標的を保ち、二成分の型を途中で取り替えない。
使われ方：compact 成分射影の指定始点の下の全試験。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：元の accessible 成分族から追加入力を保つ compact な引き戻し頂点を作る。
方針：同じ成分族の表示内の相対交互構成を元の第一脚で厳密化して貼る。
規約：元の全入力と標的、制限前の二つの成分頂点を保持する。
使われ方：指定成分始点を保つ under comma の全余錐。 -/
lemma exists_compactExtendedInputPullbackVertex_family
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : IsCardinalChangeBound κ μ)
    {K : SSet.{u}} [Quasicategory K] (hK : IsKappaSmall μ K)
    {B : SSet.{u + 1}} [Quasicategory B] (hB : IsKappaAccessible μ B)
    (C : Fin 2 → SSet.{u + 1}) [∀ c, Quasicategory (C c)]
    (L : Fin 2 → SSet.{u}) [∀ c, Quasicategory (L c)]
    (hL : ∀ c, IsKappaSmall μ (L c)) (hC : ∀ c, IsKappaAccessible μ (C c))
    (hCκ : ∀ c, Ind.HasSmallKappaFilteredColimits κ (C c))
    (hBκ : Ind.HasSmallKappaFilteredColimits κ B)
    (p : ∀ c, C c ⟶ B) (hp : F1B.EquivalenceLifting (p 0))
    (hpμ : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (p c))
    (hpκ : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (p c))
    (hpCompact : ∀ c, ∀ v, Compact.IsKappaCompact.{u, u + 1} μ v →
      Compact.IsKappaCompact.{u, u + 1} μ ((p c).app (Opposite.op ⦋0⦌) v))
    (a : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ pullback (p 0) (p 1)) (z : JoinCocone a)
    (q : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (L c) ⟶ C c)
    (hqCompact : ∀ c, ∀ v, Compact.IsKappaCompact.{u, u + 1} μ
      ((q c).app (Opposite.op ⦋0⦌) v))
    (i : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj K ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (L c)) [Mono (i 0)]
    (hi : ∀ c, i c ≫ q c = pullbackComponentInput p a c)
    (zc : ∀ c, JoinCocone (q c))
    (hzi : ∀ c, joinMap (i c) (𝟙 Δ[0]) ≫ (zc c).val = (pullbackComponentInputCocone p a z c).val) :
    Nonempty (ExtendedInputPullbackVertexData μ p a z q i hi zc hzi) := by
  let a₀ := pullbackComponentInput p a
  let z₀ := pullbackComponentInputCocone p a z
  let r := (a ≫ pullback.fst (p 0) (p 1)) ≫ p 0
  let t := mapJoinCocone (p 0) (mapJoinCocone (pullback.fst (p 0) (p 1)) z)
  have hQ : (a ≫ pullback.snd (p 0) (p 1)) ≫ p 1 = r := by
    simp only [r, Category.assoc, pullback.condition]
  have hZ : (mapJoinCocone (pullback.snd (p 0) (p 1)) z).val ≫ p 1 = t.val := by
    change (z.val ≫ pullback.snd (p 0) (p 1)) ≫ p 1 =
      (z.val ≫ pullback.fst (p 0) (p 1)) ≫ p 0
    simp only [Category.assoc, pullback.condition]
  have hpr : ∀ c, a₀ c ≫ p c = r := finitePairSection _ rfl hQ
  have hzt : ∀ c, (z₀ c).val ≫ p c = t.val := finitePairSection _ rfl hZ
  obtain ⟨v, hc, ⟨he⟩⟩ := exists_extendedInputComparison_of_accessible_components h hK hB
    C L hL hC hCκ hBκ p hpμ hpκ hpCompact q hqCompact a₀ i hi zc z₀ hzi r hpr t hzt
  exact nonempty_extendedInputPullbackVertexData_of_compatible μ p a z q i hi zc hzi
    hp hpr hzt v hc he

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
