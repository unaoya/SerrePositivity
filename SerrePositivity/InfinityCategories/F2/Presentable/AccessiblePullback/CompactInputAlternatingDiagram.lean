module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.CompactInputPresentation

/-!
概要：元の両成分の入力付き compact 表示を同じ固定始域の全相対交互図式へ接続する。
方針：accessible 性から表示を構成し、全増大余錐を揃えて共通の Ind 底へ送る。
規約：成分の表示や交互塔の存在を追加仮定にしない。
使われ方：元の入力図式を compact 成分対へ延長する中核構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：元の両成分入力の射を保つ同じ固定始域内の全相対交互図式が存在する。
方針：元の各 accessible 圏で入力付き compact 表示を構成し、同じ底の相対因子化へ渡す。
規約：同じ全入力と元の成分表示内の全添字を保持する。
使われ方：長さ κ₀ の最終 compact 成分対とその入力付き比較。 -/
lemma exists_compactInputAlternatingDiagram
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : IsCardinalChangeBound κ μ)
    {A K : SSet.{u}} [Quasicategory A] [Quasicategory K] (hK : IsKappaSmall μ K)
    (C : Fin 2 → SSet.{u + 1}) [∀ c, Quasicategory (C c)]
    (hC : ∀ c, IsKappaAccessible μ (C c))
    (p : ∀ c, C c ⟶ Ind.IndInfinity μ A)
    (hp : ∀ c, IsKappaAccessibleFunctor μ (p c))
    (hpCompact : ∀ c, ∀ v, Compact.IsKappaCompact.{u, u + 1} μ v →
      Compact.IsKappaCompact.{u, u + 1} μ ((p c).app (Opposite.op ⦋0⦌) v))
    (q : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C c)
    (hqCompact : ∀ c, ∀ v, Compact.IsKappaCompact.{u, u + 1} μ
      ((q c).app (Opposite.op ⦋0⦌) v))
    (r : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ Ind.IndInfinity μ A)
    (hq : ∀ c, q c ≫ p c = r)
    (z : ∀ c, JoinCocone (q c)) (t : JoinCocone r)
    (hz : ∀ c, (z c).val ≫ p c = t.val) :
    ∃ N : ∀ c, CompactInputPresentation μ (q c) (z c),
      ∃ F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (AlternatingIndex κ)) ⟶
          sliceOver ((SSet.yonedaEquiv (X := sliceUnder r)).symm t),
        ∃ J : ∀ c, nerve κ.ord.ToType ⟶ (N c).index,
          ∀ c, (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (alternatingSection κ c)) ≫ F =
            (SSet.uliftFunctor.{u + 1, u}).map (J c) ≫ (N c).diagram ≫
              stableInputPostcomp (q c) (p c) r (hq c) (z c) t (hz c) := by
  have hμ : Cardinal.aleph0 < μ :=
    (Cardinal.IsRegular.aleph0_le (Fact.out : κ.IsRegular)).trans_lt h.1
  let N := fun c ↦ Classical.choice
    (nonempty_compactInputPresentation_of_isKappaAccessible hμ (hC c) hK (q c) (hqCompact c) (z c))
  let P := fun c ↦ (N c).diagram ≫ stableInputPostcomp (q c) (p c) r (hq c) (z c) t (hz c)
  have hP : ∀ c, ∀ v : (N c).index _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
      ((P c ≫ sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder r)).symm t) ≫
        sliceUnderProjection r).app (Opposite.op ⦋0⦌) (ULift.up v)) := by
    intro c v
    have heq : P c ≫ sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder r)).symm t) ≫
        sliceUnderProjection r =
      (N c).diagram ≫
        sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder (q c))).symm (z c)) ≫
          sliceUnderProjection (q c) ≫ p c := by
      dsimp only [P]
      rw [Category.assoc, stableInputPostcomp_base_projection]
    rw [heq]
    exact hpCompact c _ ((N c).compact v)
  have hcol : ∀ c, IsColimitCone
      (mapJoinCocone (sliceUnderProjection r) (sliceDiagramCocone (P c))) := by
    intro c
    exact stableInputPostcomp_base_isColimitCone (q c) (p c) (hp c) r (hq c)
      (z c) t (hz c) (N c).diagram (N c).colimit_base
  have hr : ∀ v, Compact.IsKappaCompact.{u, u + 1} μ (r.app (Opposite.op ⦋0⦌) v) := by
    intro v
    rw [← hq 0]
    exact hpCompact 0 _ (hqCompact 0 v)
  obtain ⟨F, J, hJ⟩ := exists_relativeAlternatingDiagram_coslice_ind
    (I := fun c ↦ (N c).index) (P := P) h hK r hr hP hcol
  refine ⟨N, F, J, ?_⟩
  intro c
  simpa only [P, Category.assoc] using hJ c

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
