module

public import SerrePositivity.InfinityCategories.F2.Compact.NativeCosliceRepresentation
public import SerrePositivity.InfinityCategories.F2.Compact.RepresentationEdgeFactorization
public import SerrePositivity.InfinityCategories.F1.Universe.Fiber

/-!
概要：compact な源からの指定した実 coslice 点を、元の filtered 表示の一段へ因子化する。
方針：同じ coslice の実表現と既存の点因子化を使い、同じ底の辺を元の宇宙へ戻す。
規約：恒等点に限定せず、指定点と元の余錐脚を保つ。
使われ方：P-1 f2、HTT 5.5.4.13 の交互列の実段階構成。
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

/-- 指定した全 coslice 点への因子化は、同じ元の余錐脚の上の実辺として回収できる。 -/
lemma compactSource_coslice_factorization {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] {x : C _⦋0⦌}
    (hx : IsKappaCompact.{u, u + 1} κ x) {K : SSet.{u}}
    [Quasicategory K] [IsKappaFiltered κ K]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C)
    (c : JoinCocone D) (hc : IsColimitCone c)
    (t : vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) c.vertex _⦋0⦌) :
    ∃ j : K _⦋0⦌,
      ∃ w : vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x))
        (D.app _ (ULift.up j)) _⦋0⦌,
      ∃ k : (sliceUnder (SSet.yonedaEquiv.symm x)).Edge w.val t.val,
        (k.map (sliceUnderProjection (SSet.yonedaEquiv.symm x))).edge =
          (coconeTransportLeg c (ULift.up j)).edge := by
  let p := sliceUnderProjection (SSet.yonedaEquiv.symm x)
  let t' := (uliftVertexFiberIso.{u + 1, u + 2} p c.vertex).hom.app (Opposite.op ⦋0⦌)
    (ULift.up t)
  obtain ⟨i, w, k, hk⟩ := representationCocone_edge_factorization
    ((SSet.uliftFunctor.{u + 2, u + 1}).map p) (nativeCosliceRepresentation x)
    ((SSet.uliftFunctor.{u + 2, u + 1}).map D) (JoinCocone.ulift c)
    (hx.nativeCoslice_preserves K D c hc) t'
  let w₀ := ((uliftVertexFiberIso.{u + 1, u + 2} p (D.app _ i.down)).inv.app
    (Opposite.op ⦋0⦌) w).down
  let k₀ : (sliceUnder (SSet.yonedaEquiv.symm x)).Edge w₀.val t.val :=
    ⟨k.edge.down, congrArg ULift.down k.src_eq, congrArg ULift.down k.tgt_eq⟩
  refine ⟨i.down.down, w₀, k₀, ?_⟩
  exact congrArg ULift.down hk

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
