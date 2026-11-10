module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.AccessibleRelativeInputComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.RelativeInputColimits

/-!
概要：accessible 成分の異なる小さい追加入力を保った compact 比較を構成する。
方針：各入力の下で元の compact 表示を構成し、共通入力へ制限して交互塔を作る。
規約：入力付き表示の存在や相対塔の存在を追加仮定にしない。
使われ方：指定成分始点を保つ compact comma の全試験余錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：異なる小さい追加入力を持つ accessible 成分の compact な像を共通入力上で比較する。
方針：元の各表示を追加入力の下で正規化し、同じ表示添字内の交互塔へ渡す。
規約：元の各入力を保ち、元の底と対象圏には filtered 余極限だけを要求する。
使われ方：compact 成分射影の下の指定始点の保持。 -/
lemma exists_extendedInputComparison_of_accessible_components
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : IsCardinalChangeBound κ μ)
    {K : SSet.{u}} [Quasicategory K] (hK : IsKappaSmall μ K)
    {B : SSet.{u + 1}} [Quasicategory B] (hB : IsKappaAccessible μ B)
    (C : Fin 2 → SSet.{u + 1}) [∀ c, Quasicategory (C c)]
    (L : Fin 2 → SSet.{u}) [∀ c, Quasicategory (L c)]
    (hL : ∀ c, IsKappaSmall μ (L c))
    (hC : ∀ c, IsKappaAccessible μ (C c))
    (hCκ : ∀ c, Ind.HasSmallKappaFilteredColimits κ (C c))
    (hBκ : Ind.HasSmallKappaFilteredColimits κ B)
    (p : ∀ c, C c ⟶ B)
    (hpμ : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (p c))
    (hpκ : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (p c))
    (hpCompact : ∀ c, ∀ v, Compact.IsKappaCompact.{u, u + 1} μ v →
      Compact.IsKappaCompact.{u, u + 1} μ ((p c).app (Opposite.op ⦋0⦌) v))
    (q : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (L c) ⟶ C c)
    (hqCompact : ∀ c, ∀ v, Compact.IsKappaCompact.{u, u + 1} μ
      ((q c).app (Opposite.op ⦋0⦌) v))
    (q₀ : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C c)
    (i : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj K ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (L c))
    (hi : ∀ c, i c ≫ q c = q₀ c)
    (z : ∀ c, JoinCocone (q c)) (z₀ : ∀ c, JoinCocone (q₀ c))
    (hzi : ∀ c, joinMap (i c) (𝟙 Δ[0]) ≫ (z c).val = (z₀ c).val)
    (r : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ B)
    (hpr : ∀ c, q₀ c ≫ p c = r) (t : JoinCocone r)
    (hzt : ∀ c, (z₀ c).val ≫ p c = t.val) :
    ∃ v : ∀ c, (sliceOver ((SSet.yonedaEquiv (X := sliceUnder (q c))).symm (z c))) _⦋0⦌,
      (∀ c, Compact.IsKappaCompact.{u, u + 1} μ
        ((sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder (q c))).symm (z c)) ≫
          sliceUnderProjection (q c)).app (Opposite.op ⦋0⦌) (v c))) ∧
      Nonempty (VertexIso
        ((relativeInputPostcomp (q 0) (i 0) (q₀ 0) (hi 0) (z 0) (z₀ 0) (hzi 0)
          (p 0) r (hpr 0) t (hzt 0)).app (Opposite.op ⦋0⦌) (v 0))
        ((relativeInputPostcomp (q 1) (i 1) (q₀ 1) (hi 1) (z 1) (z₀ 1) (hzi 1)
          (p 1) r (hpr 1) t (hzt 1)).app (Opposite.op ⦋0⦌) (v 1))) := by
  have hμ : Cardinal.aleph0 < μ :=
    (Cardinal.IsRegular.aleph0_le (Fact.out : κ.IsRegular)).trans_lt h.1
  let N := fun c ↦ Classical.choice
    (nonempty_compactInputPresentation_of_isKappaAccessible hμ (hC c)
      (hL c) (q c) (hqCompact c) (z c))
  let T := fun c ↦ relativeInputPostcomp (q c) (i c) (q₀ c) (hi c) (z c) (z₀ c) (hzi c)
    (p c) r (hpr c) t (hzt c)
  have hT (c : Fin 2) : T c ≫
      sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder r)).symm t) ≫
        sliceUnderProjection r =
      sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder (q c))).symm (z c)) ≫
        sliceUnderProjection (q c) ≫ p c :=
    relativeInputPostcomp_base_projection (q c) (i c) (q₀ c) (hi c) (z c) (z₀ c) (hzi c)
      (p c) r (hpr c) t (hzt c)
  have hcol (c : Fin 2) : IsColimitCone (mapJoinCocone (sliceUnderProjection r)
      (sliceDiagramCocone ((N c).diagram ≫ T c))) :=
    relativeInputPostcomp_base_isColimitCone (q c) (i c) (q₀ c) (hi c) (z c) (z₀ c) (hzi c)
      (p c) (hpμ c) r (hpr c) t (hzt c) (N c).diagram (N c).colimit_base
  have hr : ∀ v, Compact.IsKappaCompact.{u, u + 1} μ (r.app (Opposite.op ⦋0⦌) v) := by
    intro v
    rw [← hpr 0, ← hi 0]
    exact hpCompact 0 _ (hqCompact 0 ((i 0).app (Opposite.op ⦋0⦌) v))
  obtain ⟨v, hc, _, he⟩ := exists_relativeInputComparison_of_isKappaAccessible_base
    h hK hB C (fun c ↦ (SSet.uliftFunctor.{u + 1, u}).obj (L c)) hCκ hBκ p hpκ
    hpCompact q z N r hr t T hT hcol
  exact ⟨v, hc, he⟩

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
