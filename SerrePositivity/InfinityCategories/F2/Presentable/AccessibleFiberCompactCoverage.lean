module

public import SerrePositivity.InfinityCategories.F2.Presentable.NativeAlternatingCompactSource
public import SerrePositivity.InfinityCategories.F2.Presentable.CompactFiberSliceRecovery
public import SerrePositivity.InfinityCategories.F2.Presentable.Accessible

/-!
概要：小余極限保存関手の固定標的 fiber の各対象上に compact 成分の実際の射を構成する。
方針：元の accessible 表示を全可算交互構成へ渡し、同値持ち上げで元の fiber に戻す。
規約：生成性や全試験余錐はこの段階では主張しない。
使われ方：fiber の小さい compact comma 模型と生成性の準備。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：元の小さい compact 表示から元の fiber 対象への compact 成分の射を構成する。
方針：全交互可算比較から得た compact 始域と恒等錐比較を元の slice 引き戻しに戻す。
規約：第二脚は任意の点射で、比較界面を入力に仮定しない。
使われ方：固定標的 fiber の compact comma 頂点の構成。 -/
lemma exists_componentCompactFiberOver_of_filteredPresentation
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {I : SSet.{u}} [Quasicategory I] [IsKappaFiltered μ I]
    {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits E) (hB : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits B)
    (p : E ⟶ B) (q : (Δ[0] : SSet.{u + 1}) ⟶ B)
    (hp : F1B.EquivalenceLifting p) (hpc : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits p)
    (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ E)
    (c : JoinCocone D) (hc : IsColimitCone c)
    (hx : SSet.yonedaEquiv.symm c.vertex = x ≫ pullback.fst p q)
    (hD : ∀ j : I _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ (D.app _ (ULift.up j)))
    (hpD : ∀ j : I _⦋0⦌,
      Compact.IsKappaCompact.{u, u + 1} μ ((D ≫ p).app _ (ULift.up j)))
    (hv : Compact.IsKappaCompact.{u, u + 1} μ (mapJoinCocone p c).vertex)
    (i : I _⦋0⦌) :
    ∃ v : (sliceOver x) _⦋0⦌,
      ComponentCompactVertex μ p q ((sliceOverProjection x).app (Opposite.op ⦋0⦌) v) := by
  obtain ⟨v, hcompact, ⟨e⟩⟩ := exists_compactSliceSource_image_identity_of_filteredPresentation
    hμ hE hB p hpc D c hc hD hpD hv i
  exact exists_componentCompactFiberOver_of_normalized_slice hμ.le p q hp x c hx v hcompact e

/-- 概要：accessible な第一成分の任意の固定標的 fiber 対象は compact 成分の対象から射を受ける。
方針：元の指定対象の小さい compact filtered 表示から可算交互構成を行う。
規約：同じ濃度での第一脚の compact 保存と固定標的の compact 性を使う。
使われ方：小さい compact 候補の対象上での被覆性。 -/
lemma exists_componentCompactFiberOver_of_isKappaAccessible
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits E) (hB : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits B) (hEμ : IsKappaAccessible μ E)
    (p : E ⟶ B) (q : (Δ[0] : SSet.{u + 1}) ⟶ B)
    (hp : F1B.EquivalenceLifting p) (hpc : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits p)
    (hpCompact : ∀ e : E _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ e →
      Compact.IsKappaCompact.{u, u + 1} μ (p.app (Opposite.op ⦋0⦌) e))
    (hq : Compact.IsKappaCompact.{u, u + 1} μ (SSet.yonedaEquiv q))
    (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q) :
    ∃ v : (sliceOver x) _⦋0⦌,
      ComponentCompactVertex μ p q ((sliceOverProjection x).app (Opposite.op ⦋0⦌) v) := by
  obtain ⟨A, hA, j, hj⟩ := hEμ.2.2
  letI := hA
  obtain ⟨I, hI, hfiltered, a, c, hv, hc⟩ := hj.presentation
    (SSet.yonedaEquiv (x ≫ pullback.fst p q))
  letI := hI
  letI := hfiltered
  have : IsFilteredInfinity I := isFilteredInfinity_of_isKappaFiltered hμ.le I
  obtain ⟨i⟩ := nonempty_vertices_of_isFilteredInfinity I
  let D := (SSet.uliftFunctor.{u + 1, u}).map a ≫ j
  have hD : ∀ k : I _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ (D.app _ (ULift.up k)) := by
    intro k
    exact hj.compact (a.app (Opposite.op ⦋0⦌) k)
  have hx : SSet.yonedaEquiv.symm c.vertex = x ≫ pullback.fst p q := by
    rw [hv, Equiv.symm_apply_apply]
  have hxd : x ≫ pullback.snd p q = 𝟙 (Δ[0] : SSet.{u + 1}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have hbase : (x ≫ pullback.fst p q) ≫ p = q := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hxd, Category.id_comp]
  have hcompactImage : Compact.IsKappaCompact.{u, u + 1} μ (mapJoinCocone p c).vertex := by
    rw [Ind.mapJoinCocone_vertex, hv, ← SSet.yonedaEquiv_comp, hbase]
    exact hq
  exact exists_componentCompactFiberOver_of_filteredPresentation hμ hE hB p q hp hpc x
    D c hc hx hD (fun k ↦ hpCompact _ (hD k)) hcompactImage i

end SerrePositivity.InfinityCategories.F2.Presentable
