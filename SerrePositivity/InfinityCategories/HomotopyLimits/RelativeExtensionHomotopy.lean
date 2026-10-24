module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.RelativeExtensionFiberEndpoint
public import SerrePositivity.InfinityCategories.F1B.Fibrations.TrivialFibrationHomotopy
public import SerrePositivity.InfinityCategories.Core.FixedDiagramHomotopy

/-!
概要：底と初期部分図式を同時に固定した、二つの相対延長の実際のホモトピー。
方針：相対関手の自明な制限の fiber 内で辺を選び、内部 Hom の辺を uncurry する。
規約：単なる終点の同型を選ばず、ホモトピー自体の底と初期制限の式を保持する。
使われ方：元の三角形 prism の長辺と標準輸送 prism の、二単体への依存を保つ比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 同じ底と同じ left anodyne な初期値を持つ二つの延長は、その両方を保つホモトピーで結べる。 -/
lemma exists_homotopy_over_fixed_extension {A D E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (β : A ⟶ B) (i : D ⟶ A)
    (hi : leftAnodyneExtensions i) (v : D ⟶ E) (hv : v ≫ p = i ≫ β)
    (W W' : A ⟶ E) (hW : W ≫ p = β) (hW' : W' ≫ p = β)
    (hWi : i ≫ W = v) (hWi' : i ≫ W' = v) :
    ∃ H : SSet.Homotopy W W',
      H.h ≫ p = fst A (Δ[1] : SSet.{u}) ≫ β ∧
      (i ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst D (Δ[1] : SSet.{u}) ≫ v := by
  have := relativeFunctorPre_trivialKanFibration p β i hi
  let x := relativeFunctorVertex p β W hW
  let y := relativeFunctorVertex p β W' hW'
  have hx : (relativeFunctorPre p β i).app (Opposite.op ⦋0⦌) x =
      relativeFunctorVertex p (i ≫ β) v hv := by
    simpa only [hWi] using relativeFunctorPre_vertex p β i W hW
  have hy : (relativeFunctorPre p β i).app (Opposite.op ⦋0⦌) y =
      relativeFunctorVertex p (i ≫ β) v hv := by
    simpa only [hWi'] using relativeFunctorPre_vertex p β i W' hW'
  obtain ⟨k, hk⟩ := exists_edge_over_trivialKanFibration (relativeFunctorPre p β i) x y
    (hx.trans hy.symm)
  let ι := vertexFiberι ((ihom A).map p) (functorVertex β)
  let a := k.map ((truncation 2).map ι)
  have hbase : ((ihom A).map p).app (Opposite.op ⦋1⦌) a.edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom A).obj B))
        (functorVertex β)).edge := by
    change (ι ≫ (ihom A).map p).app (Opposite.op ⦋1⦌) k.edge = _
    rw [vertexFiberι_comp]
    change PinchedHom.constant (functorVertex β) 1 = _
    exact pinchedConstant_one _
  have hpre : ((pre i).app E).app (Opposite.op ⦋1⦌) a.edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom D).obj E))
        (functorVertex v)).edge := by
    let ι' := vertexFiberι ((ihom D).map p) (functorVertex (i ≫ β))
    have hh := congrArg (fun s : relativeFunctorSpace p β ⟶ (ihom D).obj E ↦
      s.app (Opposite.op ⦋1⦌) k.edge) (relativeFunctorPre_ι p β i)
    change ι'.app (Opposite.op ⦋1⦌)
      ((relativeFunctorPre p β i).app (Opposite.op ⦋1⦌) k.edge) =
        ((pre i).app E).app (Opposite.op ⦋1⦌) a.edge at hh
    rw [hk, hy] at hh
    have hid := congrArg SSet.Truncated.Edge.edge
      (SSet.Truncated.Edge.map_id (relativeFunctorVertex p (i ≫ β) v hv)
        ((truncation 2).map ι'))
    exact hh.symm.trans hid
  exact ⟨simplicialHomotopyOfFunctorEdge a,
    simplicialHomotopyOfFunctorEdge_comp_eq_constant p β a hbase,
    simplicialHomotopyOfFunctorEdge_pre_eq_constant i v a hpre⟩

end
end SerrePositivity.InfinityCategories.HomotopyLimits
