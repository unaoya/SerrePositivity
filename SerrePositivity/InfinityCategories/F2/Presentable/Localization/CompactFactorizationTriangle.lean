module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactFactorization
public import SerrePositivity.InfinityCategories.Core.InitialHomotopy
public import SerrePositivity.InfinityCategories.Core.CoconeLeg

/-!
概要：compact 源の因子化を、元の辺を合成辺とする実二単体として回収する。
方針：指定 coslice 点の因子化の全辺を、余錐の脚の合成構造へ移す。
規約：後半の辺は元の filtered 余錐脚、合成辺は元の指定辺そのもの。
使われ方：HTT 5.5.4.13 の表示間の交互比較辺。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open Compact

/-- 指定辺を、元の余錐脚と合成する実二単体で一段へ因子化する。 -/
lemma compactSource_factorization_triangle {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] {x : C _⦋0⦌}
    (hx : IsKappaCompact.{u, u + 1} κ x)
    {K : SSet.{u}} [Quasicategory K] [IsKappaFiltered κ K]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C)
    (c : JoinCocone D) (hc : IsColimitCone c) (t : C.Edge x c.vertex) :
    ∃ j : K _⦋0⦌, ∃ f : C.Edge x (D.app _ (ULift.up j)),
      Nonempty (f.CompStruct (coconeTransportLeg c (ULift.up j)) t) := by
  let t₀ : (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) c.vertex) _⦋0⦌ :=
    ⟨edgeCosliceVertex t.toTruncated, by
      rw [edgeCosliceVertex_projection]
      exact (pinchedConstant_zero _).symm⟩
  obtain ⟨j, w, k, hk⟩ := compactSource_coslice_factorization hx D c hc t₀
  have hw : JoinCocone.vertex (p := SSet.yonedaEquiv.symm x) w.val =
      D.app _ (ULift.up j) := w.property.trans (pinchedConstant_zero _)
  let f : C.Edge x (D.app _ (ULift.up j)) :=
    { edge := (JoinCocone.leg w.val (𝟙 Δ[0])).edge
      src_eq := by
        have hs := (JoinCocone.leg w.val (𝟙 Δ[0])).src_eq
        change C.δ 1 (JoinCocone.leg w.val (𝟙 Δ[0])).edge =
          SSet.yonedaEquiv (𝟙 Δ[0] ≫ SSet.yonedaEquiv.symm x) at hs
        rw [Category.id_comp, Equiv.apply_symm_apply] at hs
        exact hs
      tgt_eq := (JoinCocone.leg w.val (𝟙 Δ[0])).tgt_eq.trans hw }
  have ht : (JoinCocone.leg t₀.val (𝟙 Δ[0])).edge = t.edge := by
    change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
      joinMap (𝟙 Δ[0]) (𝟙 Δ[0]) ≫
      ((joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm t.edge)) = _
    rw [joinMap_id, Category.id_comp, Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]
  let T := JoinCocone.legCompStruct k.toTruncated (𝟙 Δ[0])
  refine ⟨j, f, ⟨{ simplex := T.simplex, d₂ := T.d₂, d₀ := ?_, d₁ := ?_ }⟩⟩
  · exact T.d₀.trans hk
  · exact T.d₁.trans ht

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
