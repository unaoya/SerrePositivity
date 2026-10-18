module

public import SerrePositivity.InfinityCategories.Core.EquivalenceIntervalEdge
public import SerrePositivity.InfinityCategories.Core.EquivalencePathVertices
public import SerrePositivity.InfinityCategories.Core.EquivalencePathLifting
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting

/-!
概要：頂点の同型を可逆区間からの射で表示する。
方針：始点固定の可逆 path の可縮 fiber で辺を選び、標準区間の単射に沿って延長する。
規約：標的は quasicategory。
使われ方：Kerodon §4.5.3・4.6.4 の圏論的円柱による同型の判定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：quasicategory の同型な二頂点は可逆区間からの射の端点となる。
方針：可逆 path の始点固定の可縮 fiber の二頂点を結び、可逆区間へ持ち上げる。
規約：端点の値は零単体で厳密に指定する。
使われ方：Kerodon §4.6.4 の圏論的円柱の存在。 -/
lemma exists_equivalenceInterval_map_of_vertexIso {Y : SSet.{u}} [Quasicategory Y]
    {x y : Y _⦋0⦌} (e : VertexIso x y) :
    ∃ f : equivalenceInterval ⟶ Y,
      f.app (Opposite.op ⦋0⦌) (nerveEquiv.symm (Codiscrete.mk (ULift.up false))) = x ∧
      f.app (Opposite.op ⦋0⦌) (nerveEquiv.symm (Codiscrete.mk (ULift.up true))) = y := by
  obtain ⟨a, ha⟩ := homotopyCategory_homMk_surjective x y e.hom
  have hai : IsInvertibleEdge a := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk a)
    rw [ha]
    infer_instance
  let a₀ := SSet.Truncated.Edge.id (X := (truncation 2).obj Y) x
  have ha₀ : IsInvertibleEdge a₀ := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk a₀)
    dsimp [a₀]
    rw [SSet.Truncated.HomotopyCategory.homMk_id]
    infer_instance
  let p := equivalencePathEndpoint Y 0
  let v₀ : (vertexFiber p x) _⦋0⦌ := ⟨equivalencePathVertex a₀ ha₀, by
    rw [pinchedConstant_zero]; exact equivalencePathVertex_zero a₀ ha₀⟩
  let v₁ : (vertexFiber p x) _⦋0⦌ := ⟨equivalencePathVertex a hai, by
    rw [pinchedConstant_zero]; exact equivalencePathVertex_zero a hai⟩
  have hc := vertexFiber_isContractibleKan p x
  have := hc.kanComplex
  obtain ⟨t, _⟩ := homotopyCategory_homMk_surjective v₀ v₁
    (terminalVertexIso (hc.isTerminalVertex v₀) (hc.isTerminalVertex v₁)).hom
  have := (isContractibleKan_iff_trivialKanFibration _).1 hc
  have := TrivialKanFibration.mem (p := terminal.from (vertexFiber p x))
    equivalenceIntervalEdge inferInstance
  let sq : CommSq (SSet.yonedaEquiv.symm t.edge) equivalenceIntervalEdge
      (terminal.from (vertexFiber p x)) (terminal.from equivalenceInterval) :=
    ⟨terminal.hom_ext _ _⟩
  have hz : sq.lift.app (Opposite.op ⦋0⦌)
      (nerveEquiv.symm (Codiscrete.mk (ULift.up false))) = v₀ := by
    have hh := congrArg (fun z : (Δ[1] : SSet.{u}) ⟶ vertexFiber p x ↦
      z.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)) sq.fac_left
    rw [SSet.yonedaEquiv_symm_app] at hh
    have hd : stdSimplex.objEquiv.{u} (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        SimplexCategory.δ (1 : Fin 2) := by decide
    rw [hd] at hh
    exact hh.trans t.src_eq
  have ho : sq.lift.app (Opposite.op ⦋0⦌)
      (nerveEquiv.symm (Codiscrete.mk (ULift.up true))) = v₁ := by
    have hh := congrArg (fun z : (Δ[1] : SSet.{u}) ⟶ vertexFiber p x ↦
      z.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1)) sq.fac_left
    rw [SSet.yonedaEquiv_symm_app] at hh
    have hd : stdSimplex.objEquiv.{u} (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        SimplexCategory.δ (0 : Fin 2) := by decide
    rw [hd] at hh
    exact hh.trans t.tgt_eq
  refine ⟨sq.lift ≫ vertexFiberι p x ≫ equivalencePathEndpoint Y 1, ?_, ?_⟩
  · change (equivalencePathEndpoint Y 1).app (Opposite.op ⦋0⦌)
      ((sq.lift.app (Opposite.op ⦋0⦌) (nerveEquiv.symm (Codiscrete.mk (ULift.up false)))).val) = x
    rw [hz]
    exact equivalencePathVertex_one a₀ ha₀
  · change (equivalencePathEndpoint Y 1).app (Opposite.op ⦋0⦌)
      ((sq.lift.app (Opposite.op ⦋0⦌) (nerveEquiv.symm (Codiscrete.mk (ULift.up true)))).val) = y
    rw [ho]
    exact equivalencePathVertex_one a hai

end SerrePositivity.InfinityCategories
