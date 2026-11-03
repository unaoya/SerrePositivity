module
public import SerrePositivity.InfinityCategories.Core.FiniteShapes

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.PushoutSpanSourceFiber
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.EdgeSourceMappingTransport
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.EdgeTerminalMappingPoint

/-!
概要：pushout の fiber 比較で指定した右枝基点を、元の左枝の始点の余錐として計算する。
方針：図式の等号による表示変更が全余錐の射を変えないことを使う。
規約：同じ一次単体と全余錐の射を厳密に保持する。
使われ方：HTT 5.5.5.13–14 の元の局所性判定への基点の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u}} (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ C)

private lemma diagramChange_inv_val {K X : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (y : X _⦋0⦌) (d : (coconeMappingSpace q y) _⦋0⦌) :
    (((cosliceFiberDiagramIso h y).inv.app _ d).val).val = d.val.val := by
  cases h
  rfl

private lemma spanRightBase_val {X : SSet.{u}} (p : (horn 2 0 : SSet.{u}) ⟶ X)
    (y : X _⦋0⦌) (d : (coconeMappingSpace (horn₂₀.ι₀₂ ≫ p) y) _⦋0⦌) :
    (((spanCoconeMappingRightBase p y).app _ d).val).val =
      joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 Δ[0]) ≫ d.val.val := by
  have h := spanCoconeMappingRightBase_uncurry p y (SSet.yonedaEquiv.symm d)
  simpa only [Category.assoc, SSet.yonedaEquiv_symm_comp, sliceUnderUncurry_yoneda,
    vertexFiberι, ConcreteCategory.hom_ofHom, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk] using h

private lemma spanRightBase_change_val {X : SSet.{u}}
    (p : (horn 2 0 : SSet.{u}) ⟶ X) (q : (Δ[1] : SSet.{u}) ⟶ X)
    (h : horn₂₀.ι₀₂ ≫ p = q) (y : X _⦋0⦌)
    (d : (coconeMappingSpace q y) _⦋0⦌) :
    ((((cosliceFiberDiagramIso h y).inv ≫ spanCoconeMappingRightBase p y).app _ d).val).val =
      joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 Δ[0]) ≫ d.val.val := by
  let d' : (coconeMappingSpace (horn₂₀.ι₀₂ ≫ p) y) _⦋0⦌ :=
    (cosliceFiberDiagramIso h y).inv.app _ d
  have hd : d'.val.val = d.val.val := diagramChange_inv_val _ y d
  exact (spanRightBase_val p y d').trans
    (congrArg (fun t ↦ joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 Δ[0]) ≫ t) hd)

/-- 右枝基点を左枝の始点へ送る作用は、元の余錐の始点側への制限そのもの。 -/
lemma pushoutSpanRightBase_val (y : C _⦋0⦌)
    (d : (coconeMappingSpace (squareLeftEdge ≫ R) y) _⦋0⦌) :
    (((pushoutSpanRightBase R y).app _ d).val).val =
      joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 Δ[0]) ≫ d.val.val :=
  spanRightBase_change_val (pushoutSpan R) (squareLeftEdge ≫ R)
    (pushoutSpan_rightDiagram R) y d

/-- 指定恒等余錐の基点は、元の左辺そのものの余錐に戻る。 -/
lemma pushoutSpanRightBase_terminal_val (y : C _⦋0⦌)
    (hy : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ (squareLeftEdge ≫ R)) = y) :
    (((pushoutSpanRightBase R y).app _
      (edgeTerminalMappingPointAt (squareLeftEdge ≫ R) y hy)).val).val =
        (joinStdSimplexIso 0 0).hom ≫ squareLeftEdge ≫ R := by
  rw [pushoutSpanRightBase_val]
  exact edgeTerminalMappingPointAt_source_val (squareLeftEdge ≫ R) y hy

/-- 指定された左辺の終点を、元の四角形の同じ頂点で読む。 -/
lemma squareLeftEdge_target_of_edge {a y : C _⦋0⦌} (v : C.Edge a y)
    (h : squareLeftEdge ≫ R = SSet.yonedaEquiv.symm v.edge) :
    squareVertex R 0 1 = y := by
  have hv : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ (squareLeftEdge ≫ R)) = y := by
    rw [h, v.δ_zero_yonedaEquiv_symm, Equiv.apply_symm_apply]
  rw [stdSimplex.yonedaEquiv_δ_comp, squareLeftEdge_target] at hv
  exact hv

private lemma edgeFiber_recovered_val {a y : C _⦋0⦌}
    (g : (coconeMappingSpace (SSet.yonedaEquiv.symm a) y) _⦋0⦌) :
    (joinStdSimplexIso 0 0).hom ≫
      SSet.yonedaEquiv.symm (cosliceFiberVertexToEdge g).edge = g.val.val :=
  congrArg (fun d : (coconeMappingSpace (SSet.yonedaEquiv.symm a) y) _⦋0⦌ ↦ d.val.val)
    ((cosliceFiberVertexEquiv a y).left_inv g)

/-- 終余錐から制限した基点は、指定された元の写像空間の点そのものである。 -/
lemma pushoutSpanRightBase_terminal_of_edgeFiber {a y : C _⦋0⦌}
    (g : (coconeMappingSpace (SSet.yonedaEquiv.symm a) y) _⦋0⦌)
    (h : squareLeftEdge ≫ R = SSet.yonedaEquiv.symm (cosliceFiberVertexToEdge g).edge)
    (hy : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ (squareLeftEdge ≫ R)) = y) :
    (((pushoutSpanRightBase R y).app _
      (edgeTerminalMappingPointAt (squareLeftEdge ≫ R) y hy)).val).val = g.val.val := by
  exact (pushoutSpanRightBase_terminal_val R y hy).trans
    ((congrArg (fun e ↦ (joinStdSimplexIso 0 0).hom ≫ e) h).trans
      (edgeFiber_recovered_val g))

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
