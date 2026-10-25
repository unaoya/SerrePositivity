module

public import SerrePositivity.InfinityCategories.F2.Presentable.CompactActualSliceCocones
public import SerrePositivity.InfinityCategories.F2.Presentable.Accessible
public import SerrePositivity.InfinityCategories.Core.UniverseSSetMaps

/-!
概要：accessible な始域の固定対象上で、compact な全図式を終対象像を持つ compact 頂点へ送る。
方針：元の固定対象の compact filtered 表示へ可算交互構成を適用する。
規約：標的像の compact 性を明示し、任意の点射の全小余極限保存を使わない。
使われ方：compact fiber comma の cofinal 判定の指定始点付き延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：元の固定対象への compact 小図式に、compact で像が終対象となる全余錐を与える。
方針：同じ固定対象の生成表示を取り、元の全相対余錐の回収を使う。
規約：元の全図式と対象を保持する。
使われ方：指定始点の coslice 図式を fiber の compact 頂点へ延長する。 -/
lemma exists_accessibleSliceCocone_image_terminal
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {K : SSet.{u}} [Quasicategory K] (hK : IsKappaSmall μ K)
    {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]
    (hE : HasSmallColimits E) (hB : HasSmallColimits B) (hEμ : IsKappaAccessible μ E)
    (p : E ⟶ B) (hpc : PreservesSmallColimits p)
    (hpCompact : ∀ e, Compact.IsKappaCompact.{u, u + 1} μ e →
      Compact.IsKappaCompact.{u, u + 1} μ (p.app _ e))
    (a : (Δ[0] : SSet.{u + 1}) ⟶ E)
    (ha : Compact.IsKappaCompact.{u, u + 1} μ (SSet.yonedaEquiv (a ≫ p)))
    (r : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ sliceOver a)
    (hr : ∀ k, Compact.IsKappaCompact.{u, u + 1} μ
      ((r ≫ sliceOverProjection a).app (Opposite.op ⦋0⦌) k)) :
    ∃ c : JoinCocone r,
      Compact.IsKappaCompact.{u, u + 1} μ
        ((sliceOverProjection a).app (Opposite.op ⦋0⦌) c.vertex) ∧
      IsTerminalVertex ((sliceOverPostcomp a p).app (Opposite.op ⦋0⦌) c.vertex) := by
  obtain ⟨A, hA, j, hj⟩ := hEμ.2.2
  have := hA
  obtain ⟨I, hI, hfiltered, d, c, hv, hc⟩ := hj.presentation (SSet.yonedaEquiv a)
  have := hI
  have := hfiltered
  let D := (SSet.uliftFunctor.{u + 1, u}).map d ≫ j
  have hD : ∀ k : I _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ (D.app _ (ULift.up k)) :=
    fun k ↦ hj.compact (d.app (Opposite.op ⦋0⦌) k)
  have hx : SSet.yonedaEquiv.symm c.vertex = a := by rw [hv, Equiv.symm_apply_apply]
  have himage : Compact.IsKappaCompact.{u, u + 1} μ (mapJoinCocone p c).vertex := by
    rw [Ind.mapJoinCocone_vertex, hv, ← SSet.yonedaEquiv_comp]
    exact ha
  exact exists_compactActualSliceCocone_image_terminal hμ hK hE hB p hpc D c hc hD
    (fun k ↦ hpCompact _ (hD k)) himage a hx r hr

/-- 概要：任意の compact 始域射から、compact で像が終対象となる始域射への実辺がある。
方針：一頂点図式の全余錐の元の脚を取る。
規約：元の固定対象と指定した始点を保持する。
使われ方：元の coslice 内での余錐頂点の延長。 -/
lemma exists_accessibleSliceEdge_image_terminal
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]
    (hE : HasSmallColimits E) (hB : HasSmallColimits B) (hEμ : IsKappaAccessible μ E)
    (p : E ⟶ B) (hpc : PreservesSmallColimits p)
    (hpCompact : ∀ e, Compact.IsKappaCompact.{u, u + 1} μ e →
      Compact.IsKappaCompact.{u, u + 1} μ (p.app _ e))
    (a : (Δ[0] : SSet.{u + 1}) ⟶ E)
    (ha : Compact.IsKappaCompact.{u, u + 1} μ (SSet.yonedaEquiv (a ≫ p)))
    (v : (sliceOver a) _⦋0⦌)
    (hv : Compact.IsKappaCompact.{u, u + 1} μ ((sliceOverProjection a).app _ v)) :
    ∃ w : (sliceOver a) _⦋0⦌,
      Compact.IsKappaCompact.{u, u + 1} μ ((sliceOverProjection a).app _ w) ∧
      IsTerminalVertex ((sliceOverPostcomp a p).app (Opposite.op ⦋0⦌) w) ∧
      Nonempty ((sliceOver a).Edge v w) := by
  let s := HomotopyLimits.uliftStdSimplexIso.{u, u + 1} 0
  let r := s.hom ≫ SSet.yonedaEquiv.symm v
  have hr : ∀ k, Compact.IsKappaCompact.{u, u + 1} μ
      ((r ≫ sliceOverProjection a).app (Opposite.op ⦋0⦌) k) := by
    intro k
    have ht : r.app (Opposite.op ⦋0⦌) k = v := by
      have hs : SSet.yonedaEquiv.symm (s.hom.app (Opposite.op ⦋0⦌) k) = 𝟙 Δ[0] :=
        SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
      calc
        r.app _ k = SSet.yonedaEquiv (SSet.yonedaEquiv.symm
            (s.hom.app (Opposite.op ⦋0⦌) k) ≫ SSet.yonedaEquiv.symm v) := by
          rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply]
          rfl
        _ = v := by rw [hs, Category.id_comp, Equiv.apply_symm_apply]
    change Compact.IsKappaCompact.{u, u + 1} μ ((sliceOverProjection a).app _ (r.app _ k))
    rw [ht]
    exact hv
  obtain ⟨c, hc, ht⟩ := exists_accessibleSliceCocone_image_terminal hμ
    (isKappaSmall_of_finite hμ.le (Δ[0] : SSet.{u})) hE hB hEμ p hpc hpCompact a ha r hr
  let k : ((SSet.uliftFunctor.{u + 1, u}).obj (Δ[0] : SSet.{u})) _⦋0⦌ :=
    SSet.yonedaEquiv s.inv
  have hk : r.app (Opposite.op ⦋0⦌) k = v := by
    change (s.hom ≫ SSet.yonedaEquiv.symm v).app _ (SSet.yonedaEquiv s.inv) = v
    rw [← SSet.yonedaEquiv_comp, ← Category.assoc, Iso.inv_hom_id, Category.id_comp,
      Equiv.apply_symm_apply]
  have e := Compact.coconeTransportLeg c k
  rw [hk] at e
  exact ⟨c.vertex, hc, ht, ⟨e⟩⟩

end SerrePositivity.InfinityCategories.F2.Presentable
