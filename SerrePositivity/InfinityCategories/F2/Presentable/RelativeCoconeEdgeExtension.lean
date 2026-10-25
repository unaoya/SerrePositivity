module

public import SerrePositivity.InfinityCategories.F2.Presentable.CoconeSpecifiedEdgeExtension
public import SerrePositivity.InfinityCategories.Core.CosliceEndpointFibration
public import SerrePositivity.InfinityCategories.Core.InnerPullback

/-!
概要：元の余錐と指定辺を、指定した基底の余錐の辺全体に沿って同時に延長する。
方針：相対 coslice 射影の left fibration 性を使い、同じ基底の全辺を輸送する。
規約：基底の高次整合を指定し、点ごとの像の一致で代用しない。
使われ方：引き戻しの交互列の比較を元の対象の上で構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：指定辺と基底の全余錐辺を、同じ元の余錐から始まる一つの余錐辺へ持ち上げる。
方針：相対 coslice 射影への引き戻し内の同じ辺を、標準輸送辺で持ち上げる。
規約：元の射は inner fibration、元と基底は quasicategory。
使われ方：元の対象の上で指定辺を保つ可算図式を選ぶ。 -/
lemma exists_relativeCocone_edge_extension {K X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y) [InnerFibration p]
    {F : K ⟶ X} (c : JoinCocone F) (t : (Δ[1] : SSet.{u}) ⟶ X)
    (C : (Δ[1] : SSet.{u}) ⟶ sliceUnder (F ≫ p))
    (ht : SSet.stdSimplex.δ (1 : Fin 2) ≫ t =
      SSet.yonedaEquiv.symm c ≫ sliceUnderProjection F)
    (hC : SSet.stdSimplex.δ (1 : Fin 2) ≫ C =
      SSet.yonedaEquiv.symm c ≫ sliceUnderPostcomp F p)
    (hp : t ≫ p = C ≫ sliceUnderProjection (F ≫ p)) :
    ∃ d : (Δ[1] : SSet.{u}) ⟶ sliceUnder F,
      SSet.stdSimplex.δ (1 : Fin 2) ≫ d = SSet.yonedaEquiv.symm c ∧
      d ≫ sliceUnderProjection F = t ∧ d ≫ sliceUnderPostcomp F p = C := by
  let r := cosliceEndpointMap F p
  let T := pullback.lift t C hp
  have h₀ : SSet.stdSimplex.δ (1 : Fin 2) ≫ T = SSet.yonedaEquiv.symm c ≫ r := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst, cosliceEndpointMap_fst, r, T] using ht
    · simpa only [Category.assoc, pullback.lift_snd, cosliceEndpointMap_snd, r, T] using hC
  let γ : (pullback p (sliceUnderProjection (F ≫ p))).Edge
      (r.app (Opposite.op ⦋0⦌) c)
      (SSet.yonedaEquiv (SSet.stdSimplex.δ (0 : Fin 2) ≫ T)) :=
    { edge := SSet.yonedaEquiv T
      src_eq := by
        change (pullback p (sliceUnderProjection (F ≫ p))).δ 1 (SSet.yonedaEquiv T) =
          r.app (Opposite.op ⦋0⦌) c
        rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, h₀, SSet.yonedaEquiv_comp,
          Equiv.apply_symm_apply]
      tgt_eq := by
        change (pullback p (sliceUnderProjection (F ≫ p))).δ 0 (SSet.yonedaEquiv T) = _
        rw [← SSet.stdSimplex.yonedaEquiv_δ_comp] }
  let v := initialFiberVertexAt r c (r.app (Opposite.op ⦋0⦌) c) rfl
  let k := standardTransportPointEdge r γ v
  let d := SSet.yonedaEquiv.symm k.edge
  have hk := standardTransportPointEdge_projection r γ v
  change r.app (Opposite.op ⦋1⦌) k.edge = SSet.yonedaEquiv T at hk
  have hd : d ≫ r = T := by
    simpa only [SSet.yonedaEquiv_symm_comp, Equiv.symm_apply_apply, d] using
      congrArg (fun s : (pullback p (sliceUnderProjection (F ≫ p))) _⦋1⦌ ↦
        SSet.yonedaEquiv.symm s) hk
  refine ⟨d, k.δ_one_yonedaEquiv_symm, ?_, ?_⟩
  · have h := congrArg (fun a ↦ a ≫ pullback.fst p (sliceUnderProjection (F ≫ p))) hd
    simpa only [Category.assoc, r, cosliceEndpointMap_fst, T, pullback.lift_fst] using h
  · have h := congrArg (fun a ↦ a ≫ pullback.snd p (sliceUnderProjection (F ≫ p))) hd
    simpa only [Category.assoc, r, cosliceEndpointMap_snd, T, pullback.lift_snd] using h

/-- 概要：元の全余錐と右辺を、指定された基底の全 join 図式を保って延長する。
方針：基底を余錐圏の辺へ curry し、相対辺の持ち上げを uncurry する。
規約：全 join 図式の射影を厳密な等式で指定する。
使われ方：元の対象の上での交互列の高次整合の延長。 -/
lemma exists_relativeJoin_edge_extension {K X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y) [InnerFibration p]
    {F : K ⟶ X} (c : JoinCocone F) (t : (Δ[1] : SSet.{u}) ⟶ X)
    (H : join K (Δ[1] : SSet.{u}) ⟶ Y)
    (ht : SSet.stdSimplex.δ (1 : Fin 2) ≫ t =
      SSet.yonedaEquiv.symm c ≫ sliceUnderProjection F)
    (hF : joinInl K Δ[1] ≫ H = F ≫ p)
    (hzero : joinMap (𝟙 K) (SSet.stdSimplex.δ (1 : Fin 2)) ≫ H = c.val ≫ p)
    (hright : joinInr K Δ[1] ≫ H = t ≫ p) :
    ∃ G : join K (Δ[1] : SSet.{u}) ⟶ X,
      joinInl K Δ[1] ≫ G = F ∧
      joinMap (𝟙 K) (SSet.stdSimplex.δ (1 : Fin 2)) ≫ G = c.val ∧
      joinInr K Δ[1] ≫ G = t ∧ G ≫ p = H := by
  let C := sliceUnderCurry H hF
  have hC : SSet.stdSimplex.δ (1 : Fin 2) ≫ C =
      SSet.yonedaEquiv.symm c ≫ sliceUnderPostcomp F p := by
    apply sliceUnderUncurry_injective (F ≫ p)
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_postcomp,
      sliceUnderUncurry_yoneda]
    simpa only [C, sliceUnderUncurry_curry] using hzero
  have hp : t ≫ p = C ≫ sliceUnderProjection (F ≫ p) := by
    dsimp only [C]
    rw [sliceUnderCurry_projection]
    exact hright.symm
  obtain ⟨d, hd₀, hdt, hdC⟩ := exists_relativeCocone_edge_extension p c t C ht hC hp
  refine ⟨sliceUnderUncurry d, sliceUnderUncurry_fixed d, ?_, ?_, ?_⟩
  · rw [← sliceUnderUncurry_precomp, hd₀, sliceUnderUncurry_yoneda]
  · exact (sliceUnderUncurry_projection d).trans hdt
  · rw [← sliceUnderUncurry_postcomp, hdC]
    exact sliceUnderUncurry_curry H hF

end SerrePositivity.InfinityCategories.F2.Presentable
