module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportEdgeHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.TransportBaseTargetLeg
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFunctorHom

/-!
概要：元のcocartesian輸送の終点比較を、指定した二つの辺の因子分解式とともに取り出す。
方針：既存の持ち上げ空間と比較同型を使い、cosliceの脚の法則で辺との両立を評価する。
規約：HTT §2.4.1、Kerodon §5.1（Tag 01T1）の既存輸送の計算法則。
使われ方：S8 の指定余単位と大域比較の成分の一致。存在だけの頂点同型に置き換えない。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 基底の同じ辺の類による既存の終点比較は、元の二つの辺との合成式を持つ。 -/
lemma exists_kanTransportEndVertexIso_with_factorization_of_homMk_eq
    {E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B) [CocartesianHornFibration p]
    (b : B _⦋0⦌) {y z : E _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj E) (SSet.yonedaEquiv a) y)
    (f : Truncated.Edge (X := (truncation 2).obj E) (SSet.yonedaEquiv a) z)
    (hy : p.app (Opposite.op ⦋0⦌) y = b) (hz : p.app (Opposite.op ⦋0⦌) z = b)
    (he : HasCocartesianHornLifting p e) (hf : HasCocartesianHornLifting p f)
    (h : Truncated.HomotopyCategory.homMk (transportBaseEdge a p b e hy) =
      Truncated.HomotopyCategory.homMk (transportBaseEdge a p b f hz)) :
    ∃ (v w : (vertexFiber p b) _⦋0⦌) (hv : v.val = y) (hw : w.val = z)
      (i : VertexIso v w),
      Truncated.HomotopyCategory.homMk e ≫ eqToHom (congrArg HomotopyCategory.mk hv.symm) ≫
        (hoFunctor.map (vertexFiberι p b)).toFunctor.map i.hom ≫
          eqToHom (congrArg HomotopyCategory.mk hw) = Truncated.HomotopyCategory.homMk f := by
  let t := transportBaseEdgeVertex a p b e hy he
  let u := transportBaseEdgeVertex a p b f hz hf
  have hh : Truncated.HomotopyCategory.homMk
      (cosliceFiberEdge (a ≫ p) b ((transportBaseFiberMap a p b).app _ t)) =
        Truncated.HomotopyCategory.homMk
          (cosliceFiberEdge (a ≫ p) b ((transportBaseFiberMap a p b).app _ u)) := by
    rw [transportBaseEdgeVertex_base_edge, transportBaseEdgeVertex_base_edge]
    exact h
  obtain ⟨i, hi⟩ := transportBaseFiberTarget_nonempty_iso_with_leg_of_homMk_eq a p b t u hh
  let J := vertexFiberι (cocartesianCosliceProjection a p ≫
    sliceUnderProjection (a ≫ p)) b ≫ cocartesianCosliceι a p
  have hv := transportBaseEdgeVertex_target_val a p b e hy he
  have hw := transportBaseEdgeVertex_target_val a p b f hz hf
  have hx : SSet.yonedaEquiv ((𝟙 (Δ[0] : SSet.{u})) ≫ a) = SSet.yonedaEquiv a := by
    rw [Category.id_comp]
  have heq : (JoinCocone.leg (J.app _ t) (𝟙 Δ[0])).edge = e.edge := by
    change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
      joinMap (𝟙 Δ[0]) (𝟙 Δ[0]) ≫ (joinStdSimplexIso 0 0).hom ≫
        SSet.yonedaEquiv.symm e.edge) = _
    rw [joinMap_id, Category.id_comp, Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]
  have hfq : (JoinCocone.leg (J.app _ u) (𝟙 Δ[0])).edge = f.edge := by
    change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
      joinMap (𝟙 Δ[0]) (𝟙 Δ[0]) ≫ (joinStdSimplexIso 0 0).hom ≫
        SSet.yonedaEquiv.symm f.edge) = _
    rw [joinMap_id, Category.id_comp, Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]
  have heh := homMk_transport hx hv (JoinCocone.leg (J.app _ t) (𝟙 Δ[0])) e heq
  have hfh := homMk_transport hx hw (JoinCocone.leg (J.app _ u) (𝟙 Δ[0])) f hfq
  refine ⟨_, _, hv, hw, i, ?_⟩
  calc
    _ = eqToHom (congrArg HomotopyCategory.mk hx).symm ≫
        (Truncated.HomotopyCategory.homMk (JoinCocone.leg (J.app _ t) (𝟙 Δ[0])) ≫
          (hoFunctor.map (vertexFiberι p b)).toFunctor.map i.hom) ≫
            eqToHom (congrArg HomotopyCategory.mk hw) := by
      rw [← heh]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    _ = _ := by rw [hi]; exact hfh

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
