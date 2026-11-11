module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactFactorization
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreCoconeLeg

/-!
概要：compact 源の因子化を、元の辺を合成辺とする実二単体として回収する。
方針：指定 coslice 点の因子化の全辺を、余錐の脚の合成構造へ移す。
規約：後半の辺は元の filtered 余錐脚、合成辺は元の指定辺そのもの。
使われ方：HTT 5.5.4.13 の表示間の交互比較辺。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 指定辺を、元の余錐脚と合成する実二単体で一段へ因子化する。 -/
lemma compactSource_factorization_triangle {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] {x : C _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ x)
    {K : SSet.{u}} [Quasicategory K] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ K]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (t : C.Edge x c.vertex) :
    ∃ j : K _⦋0⦌, ∃ f : C.Edge x (D.app _ (ULift.up j)),
      Nonempty (f.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c (ULift.up j)) t) := by
  let t₀ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) c.vertex) _⦋0⦌ :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.edgeCosliceVertex t.toTruncated, by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.edgeCosliceVertex_projection]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _).symm⟩
  obtain ⟨j, w, k, hk⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactSource_coslice_factorization hx D c hc t₀
  have hw : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex (p := SSet.yonedaEquiv.symm x) w.val =
      D.app _ (ULift.up j) := w.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _)
  let f : C.Edge x (D.app _ (ULift.up j)) :=
    { edge := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.leg w.val (𝟙 Δ[0])).edge
      src_eq := by
        have hs := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.leg w.val (𝟙 Δ[0])).src_eq
        change C.δ 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.leg w.val (𝟙 Δ[0])).edge =
          SSet.yonedaEquiv (𝟙 Δ[0] ≫ SSet.yonedaEquiv.symm x) at hs
        rw [Category.id_comp, Equiv.apply_symm_apply] at hs
        exact hs
      tgt_eq := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.leg w.val (𝟙 Δ[0])).tgt_eq.trans hw }
  have ht : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.leg t₀.val (𝟙 Δ[0])).edge = t.edge := by
    change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (𝟙 Δ[0]) ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm t.edge)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id, Category.id_comp, Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]
  let T := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.legCompStruct k.toTruncated (𝟙 Δ[0])
  refine ⟨j, f, ⟨{ simplex := T.simplex, d₂ := T.d₂, d₀ := ?_, d₁ := ?_ }⟩⟩
  · exact T.d₀.trans hk
  · exact T.d₁.trans ht

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
