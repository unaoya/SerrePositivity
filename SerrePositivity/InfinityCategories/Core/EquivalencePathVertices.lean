module

public import SerrePositivity.InfinityCategories.Core.EquivalencePathInnerFibration

/-!
概要：可逆な辺を path の頂点として表示し、置換の頂点上の全射性を示す。
方針：ホモトピー圏の同型を実際の辺で表し、引き戻しへ含める。
規約：本質的全射性は元の関手に仮定する。
使われ方：Kerodon §4.8.1、Theorem 4.8.4.1 の射の置換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：可逆な辺が表す可逆 path の頂点。
方針：辺の Yoneda 表示を関手の頂点とし、全部分複体に含める。
規約：標的に quasicategory 性は不要。
使われ方：Kerodon §4.5.3、§4.8.1 の頂点の表示。 -/
def equivalencePathVertex {Y : SSet.{u}} {x y : Y _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj Y) x y)
    (he : IsInvertibleEdge e) : (equivalencePath Y) _⦋0⦌ :=
  ⟨functorVertex (SSet.yonedaEquiv.symm e.edge), by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    subst α
    rw [op_id, CategoryTheory.Functor.map_id_apply]
    unfold IsEquivalencePathVertex
    rw [intervalFunctorVertexEdge_functorVertex, Equiv.apply_symm_apply]
    exact (isInvertibleEdge_congr (e := edgeOfSimplex e.edge) (f := e) rfl).mpr he⟩

/-- 概要：辺からの path の始点は元の辺の始点。
方針：区間の零頂点で Yoneda 表示を評価する。
規約：与えた辺の端点を使う。
使われ方：Kerodon §4.5.3 の始点の識別。 -/
lemma equivalencePathVertex_zero {Y : SSet.{u}} {x y : Y _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj Y) x y) (he : IsInvertibleEdge e) :
    (equivalencePathEndpoint Y 0).app (Opposite.op ⦋0⦌) (equivalencePathVertex e he) = x := by
  change (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)).app (Opposite.op ⦋0⦌)
    (functorVertex (SSet.yonedaEquiv.symm e.edge)) = x
  rw [evaluateFunctorAt_functorVertex, SSet.yonedaEquiv_symm_app]
  have h : stdSimplex.objEquiv.{u} (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      SimplexCategory.δ (1 : Fin 2) := by decide
  rw [h]
  exact e.src_eq

/-- 概要：辺からの path の終点は元の辺の終点。
方針：区間の一頂点で Yoneda 表示を評価する。
規約：与えた辺の端点を使う。
使われ方：Kerodon §4.5.3 の終点の識別。 -/
lemma equivalencePathVertex_one {Y : SSet.{u}} {x y : Y _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj Y) x y) (he : IsInvertibleEdge e) :
    (equivalencePathEndpoint Y 1).app (Opposite.op ⦋0⦌) (equivalencePathVertex e he) = y := by
  change (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1)).app (Opposite.op ⦋0⦌)
    (functorVertex (SSet.yonedaEquiv.symm e.edge)) = y
  rw [evaluateFunctorAt_functorVertex, SSet.yonedaEquiv_symm_app]
  have h : stdSimplex.objEquiv.{u} (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      SimplexCategory.δ (0 : Fin 2) := by decide
  rw [h]
  exact e.tgt_eq

/-- 概要：本質的全射な関手の path による置換は頂点上で全射。
方針：各標的頂点へのホモトピー圏の同型を可逆な辺で表し、引き戻しへ送る。
規約：標的 Y が quasicategory、始域の quasicategory 性は不要。
使われ方：Kerodon Theorem 4.8.4.1 の全射な射への還元。 -/
lemma IsEssentiallySurjective.equivalencePathReplacementMap_surjective {X Y : SSet.{u}}
    [Quasicategory Y] {f : X ⟶ Y} (hf : IsEssentiallySurjective f) :
    Function.Surjective ((equivalencePathReplacementMap f).app (Opposite.op ⦋0⦌)) := by
  intro y
  obtain ⟨x, ⟨e⟩⟩ := hf y
  obtain ⟨s, hs⟩ := homotopyCategory_homMk_surjective (f.app (Opposite.op ⦋0⦌) x) y e.hom
  have he : IsInvertibleEdge s := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk s)
    rw [hs]
    infer_instance
  let v := equivalencePathVertex s he
  have hv : (equivalencePathEndpoint Y 0).app (Opposite.op ⦋0⦌) v =
      f.app (Opposite.op ⦋0⦌) x := equivalencePathVertex_zero s he
  let a := SSet.yonedaEquiv.symm v
  let b := SSet.yonedaEquiv.symm x
  have hw : a ≫ equivalencePathEndpoint Y 0 = b ≫ f := by
    rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, hv]
  let l := pullback.lift a b hw
  refine ⟨SSet.yonedaEquiv l, ?_⟩
  have hl : l ≫ equivalencePathReplacementMap f = a ≫ equivalencePathEndpoint Y 1 := by
    change l ≫ pullback.fst (equivalencePathEndpoint Y 0) f ≫ equivalencePathEndpoint Y 1 = _
    rw [← Category.assoc, pullback.lift_fst]
  have h := congrArg SSet.yonedaEquiv hl
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
  exact h.trans (equivalencePathVertex_one s he)

end SerrePositivity.InfinityCategories
