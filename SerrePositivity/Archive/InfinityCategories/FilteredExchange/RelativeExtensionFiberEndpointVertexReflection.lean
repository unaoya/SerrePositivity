module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeExtensionFiberEndpoint

/-!
概要：指定 fiber 終点の頂点等式から、元の全延長の実終点の等式を回収する。
方針：同じ制限射の標準 fiber 持ち上げで頂点を計算し、関手頂点の単射性を使う。
規約：同型の存在や HEq から端点等式を推測しない。
使われ方：零面の比較の正規化した両端を実最後辺の境界へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：同じ終点評価の頂点等式は、元の延長の同じ実終点の表示と同値。方針：標準 fiber 持ち上げで反映。
規約：元の制限射を保持。使われ方：零面の実終点の回収。 -/
lemma relativeExtensionFiberEndpoint_vertex_iff {A D C E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ a)
    (j : C ⟶ A) (b : B _⦋0⦌) (hj : j ≫ a = SSet.const b)
    (W : A ⟶ E) (hW : W ≫ p = a) (hWi : i ≫ W = v)
    (g : C ⟶ vertexFiber p b) :
    (relativeExtensionFiberEndpoint p a i v hv j b hj).app _
      (relativeFunctorExtensionSpaceVertexEquiv p a i v hv ⟨W, hW, hWi⟩) = functorVertex g ↔
        j ≫ W = g ≫ vertexFiberι p b := by
  constructor
  · intro h
    let k := vertexFiberLift p b (j ≫ W) (by rw [Category.assoc, hW, hj])
    have hk : j ≫ W = k ≫ vertexFiberι p b := (vertexFiberLift_ι _ _ _ _).symm
    have he := relativeExtensionFiberEndpoint_vertex p a i v hv j b hj W hW hWi k hk
    have hkg : k = g := (functorVertexEquiv _ _).injective (he.symm.trans h)
    exact hk.trans (congrArg (fun t => t ≫ vertexFiberι p b) hkg)
  · exact relativeExtensionFiberEndpoint_vertex p a i v hv j b hj W hW hWi g

end SerrePositivity.InfinityCategories.F2
