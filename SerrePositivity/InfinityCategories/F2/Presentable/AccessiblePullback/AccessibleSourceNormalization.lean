module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.NativeSourceNormalization
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.CompactFactorizationTransport

/-!
概要：accessible 圏の元の生成表示を小さい compact 入力図式の下へ正規化する。
方針：全 compact 図式の因子化を元の表示の一段で選び、同じ全表示を一点下から持ち上げる。
規約：元の圏の全小余極限を追加仮定にしない。
使われ方：元の両成分の入力を伴う filtered 表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：accessible 圏の元の filtered 表示は、小さい compact 入力図式を保持して正規化できる。
方針：元の全余錐の一段因子化と入力付き全表示の回収を接続する。
規約：元の表示添字の一点下への厳密な制限を底の図式として返す。
使われ方：元の両成分表示を固定始域内の交互構成へ渡す。 -/
lemma exists_nativeSourceNormalization_of_isKappaAccessible
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {C : SSet.{u + 1}} [Quasicategory C] (hC : IsKappaAccessible μ C)
    {K : SSet.{u}} [Quasicategory K] (hK : IsKappaSmall μ K)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C)
    (hq : ∀ v, Compact.IsKappaCompact.{u, u + 1} μ (q.app (Opposite.op ⦋0⦌) v))
    {I : SSet.{u}} [Quasicategory I] [IsKappaFiltered μ I]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ C)
    (c : JoinCocone D) (hc : IsColimitCone c)
    (z : JoinCocone q) (hz : z.vertex = c.vertex) :
    ∃ i : I _⦋0⦌, IsKappaFiltered μ (sliceUnder (SSet.yonedaEquiv.symm i)) ∧
      ∃ F : (SSet.uliftFunctor.{u + 1, u}).obj (sliceUnder (SSet.yonedaEquiv.symm i)) ⟶
          sliceUnder q,
        F ≫ sliceUnderProjection q =
          (SSet.uliftFunctor.{u + 1, u}).map
            (sliceUnderProjection (SSet.yonedaEquiv.symm i)) ≫ D ∧
        ∃ c' : JoinCocone F, IsColimitCone c' ∧ c'.vertex = z ∧
          c'.val ≫ sliceUnderProjection q =
            (c.restrict ((SSet.uliftFunctor.{u + 1, u}).map
              (sliceUnderProjection (SSet.yonedaEquiv.symm i)))).val := by
  let t : (vertexFiber (sliceUnderProjection q) c.vertex) _⦋0⦌ :=
    ⟨z, hz.trans (pinchedConstant_zero _).symm⟩
  obtain ⟨i, w, k, hk⟩ := compactDiagramFactorization_of_isKappaAccessible hμ hC
    hK q hq D c hc t
  have hw : JoinCocone.vertex (p := q) w.val = D.app (Opposite.op ⦋0⦌) (ULift.up i) :=
    w.property.trans (pinchedConstant_zero _)
  exact ⟨i, exists_nativeSourceNormalization_of_factorization
    (Fact.out : μ.IsRegular) D c hc i hw k hk⟩

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
