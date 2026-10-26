module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.RelativeInputComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.IndInputReflection

/-!
概要：異なる追加入力を保持した compact 比較を元の accessible な底へ戻す。
方針：共通 Ind 解像へ比較全体を送り、固定共通入力上の同型を反映する。
規約：元の各入力と元の底を保ち、表示の存在を accessible 性から構成する。
使われ方：compact comma の両成分射影の cofinal 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：元の accessible な底で追加入力を持つ compact 成分対の像を比較できる。
方針：同じ表示内で Ind 上の相対交互構成を行い、固定共通入力上の同型を降下する。
規約：各成分の追加入力は保持し、比較だけを共通入力に制限する。
使われ方：指定した成分始点を保つ compact 余錐の構成。 -/
lemma exists_relativeInputComparison_of_isKappaAccessible_base
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : IsCardinalChangeBound κ μ)
    {K : SSet.{u}} [Quasicategory K] (hK : IsKappaSmall μ K)
    {B : SSet.{u + 1}} [Quasicategory B] (hB : IsKappaAccessible μ B)
    (C L : Fin 2 → SSet.{u + 1}) [∀ c, Quasicategory (C c)] [∀ c, Quasicategory (L c)]
    (hCκ : ∀ c, Ind.HasSmallKappaFilteredColimits κ (C c))
    (hBκ : Ind.HasSmallKappaFilteredColimits κ (B))
    (p : ∀ c, C c ⟶ B)
    (hpκ : ∀ c, IsKappaAccessibleFunctor κ (p c))
    (hpCompact : ∀ c, ∀ v, Compact.IsKappaCompact.{u, u + 1} μ v →
      Compact.IsKappaCompact.{u, u + 1} μ ((p c).app (Opposite.op ⦋0⦌) v))
    (q : ∀ c, L c ⟶ C c) (z : ∀ c, JoinCocone (q c))
    (N : ∀ c, CompactInputPresentation μ (q c) (z c))
    (r : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ B)
    (hr : ∀ v, Compact.IsKappaCompact.{u, u + 1} μ (r.app (Opposite.op ⦋0⦌) v))
    (t : JoinCocone r)
    (T : ∀ c, sliceOver ((SSet.yonedaEquiv (X := sliceUnder (q c))).symm (z c)) ⟶
      sliceOver ((SSet.yonedaEquiv (X := sliceUnder r)).symm t))
    (hT : ∀ c, T c ≫ sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder r)).symm t) ≫
        sliceUnderProjection r =
      sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder (q c))).symm (z c)) ≫
        sliceUnderProjection (q c) ≫ p c)
    (hcol : ∀ c, IsColimitCone (mapJoinCocone (sliceUnderProjection r)
      (sliceDiagramCocone ((N c).diagram ≫ T c)))) :
    ∃ v : ∀ c, (sliceOver ((SSet.yonedaEquiv (X := sliceUnder (q c))).symm (z c))) _⦋0⦌,
      (∀ c, Compact.IsKappaCompact.{u, u + 1} μ
        ((sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder (q c))).symm (z c)) ≫
          sliceUnderProjection (q c)).app (Opposite.op ⦋0⦌) (v c))) ∧
      (∀ c, Compact.IsKappaCompact.{u, u + 1} μ
        ((sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder (q c))).symm (z c)) ≫
          sliceUnderProjection (q c) ≫ p c).app (Opposite.op ⦋0⦌) (v c))) ∧
      Nonempty (VertexIso ((T 0).app (Opposite.op ⦋0⦌) (v 0))
        ((T 1).app (Opposite.op ⦋0⦌) (v 1))) := by
  obtain ⟨R⟩ := nonempty_indBaseResolution_of_isKappaAccessible hB
  let β := R.comparison
  have heβ := R.comparison_isQCatEquivalence
  let p' := fun c ↦ p c ≫ β
  have hpκ' : ∀ c, IsKappaAccessibleFunctor κ (p' c) := fun c ↦
    (hpκ c).comp (equivalence_preservesSmallKappaFilteredColimits κ heβ)
  have hcompact : ∀ c, ∀ v, Compact.IsKappaCompact.{u, u + 1} μ v →
      Compact.IsKappaCompact.{u, u + 1} μ ((p' c).app (Opposite.op ⦋0⦌) v) := by
    intro c v hv
    exact isKappaCompact_image_of_equivalence heβ.choose
      ((p c).app (Opposite.op ⦋0⦌) v) (hpCompact c v hv)
  let W := stableInputPostcomp r β (r ≫ β) rfl t (mapJoinCocone β t) rfl
  let T' := fun c ↦ T c ≫ W
  have hT' : ∀ c, T' c ≫
      sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder (r ≫ β))).symm
        (mapJoinCocone β t)) ≫ sliceUnderProjection (r ≫ β) =
      sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder (q c))).symm (z c)) ≫
        sliceUnderProjection (q c) ≫ p' c := by
    intro c
    dsimp only [T', W, p']
    rw [Category.assoc, stableInputPostcomp_base_projection]
    calc
      _ = (T c ≫ sliceOverProjection _ ≫ sliceUnderProjection r) ≫ β := by
        simp only [Category.assoc]
      _ = _ := by rw [hT c]; simp only [Category.assoc]
  have hcol' (c : Fin 2) : IsColimitCone (mapJoinCocone (sliceUnderProjection (r ≫ β))
      (sliceDiagramCocone ((N c).diagram ≫ T' c))) := by
    exact stableInputPostcomp_base_isColimitCone r β
      (equivalence_preservesSmallKappaFilteredColimits μ heβ)
      (r ≫ β) rfl t (mapJoinCocone β t) rfl ((N c).diagram ≫ T c) (hcol c)
  have hr' : ∀ v, Compact.IsKappaCompact.{u, u + 1} μ ((r ≫ β).app (Opposite.op ⦋0⦌) v) := by
    intro v
    exact isKappaCompact_image_of_equivalence heβ.choose _ (hr v)
  obtain ⟨v, hc, hpc, he⟩ := exists_relativeInputComparison_of_presentations h hK C L hCκ
    (R.model_hasSmallKappaFilteredColimits hBκ) p' hpκ' hcompact q z N
    (r ≫ β) hr' (mapJoinCocone β t) T' hT' hcol'
  have hback := R.nonempty_inputVertexIso_of_comparison r t he
  refine ⟨v, hc, ?_, hback⟩
  intro c
  exact hpCompact c _ (hc c)

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
