module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingVertices

/-!
概要：両端固定の区間模型の頂点と、その端点を持つ実際の辺の全単射。
方針：区間からの射の関手頂点の全単射を境界の固定条件へ制限する。
規約：標的の充填性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、写像空間の比較射のすべての頂点を個別の変換として扱う。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：区間の固定境界図式の始点の面は始点の Yoneda 射。
方針：零次元の定値単体を計算する。
規約：欠ける頂点の番号は 1。
使われ方：Kerodon §4.6.6（Tag 04HY）、区間模型の頂点から辺の始点条件を回収する。 -/
lemma intervalMappingBoundary_face_one {X : SSet.{u}} (x y : X _⦋0⦌) :
    boundary.ι (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary x y = SSet.yonedaEquiv.symm x := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 0 = x
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero x

/-- 概要：区間の固定境界図式の終点の面は終点の Yoneda 射。
方針：零次元の定値単体を計算する。
規約：欠ける頂点の番号は 0。
使われ方：Kerodon §4.6.6（Tag 04HY）、区間模型の頂点から辺の終点条件を回収する。 -/
lemma intervalMappingBoundary_face_zero {X : SSet.{u}} (x y : X _⦋0⦌) :
    boundary.ι (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary x y = SSet.yonedaEquiv.symm y := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y 0 = y
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero y

/-- 概要：両端固定の区間模型の任意の頂点から、その端点を持つ実際の辺を回収する。
方針：関手頂点を区間からの射へ戻し、境界の条件を二端点の条件へ移す。
規約：回収する一単体は戻した射の Yoneda 単体。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、写像空間の比較の任意の頂点を実際の変換として読む。 -/
noncomputable def intervalMappingEdgeOfVertex {X : SSet.{u}} {x y : X _⦋0⦌}
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) _⦋0⦌) : SSet.Edge x y := by
  let H := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] : SSet.{u}) X).symm v.val
  have hH : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H = v.val := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply v.val
  have hb : (boundary 1).ι ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary x y := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
    change ((pre (boundary 1).ι).app X).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary x y)
    rw [hH]
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] using v.property
  refine ⟨SSet.yonedaEquiv H, ?_, ?_⟩
  · have h := congrArg (fun f => SSet.yonedaEquiv (boundary.ι (1 : Fin 2) ≫ f)) hb
    rw [← Category.assoc, boundary.ι_ι, intervalMappingBoundary_face_one,
      Equiv.apply_symm_apply, stdSimplex.yonedaEquiv_δ_comp] at h
    exact h
  · have h := congrArg (fun f => SSet.yonedaEquiv (boundary.ι (0 : Fin 2) ≫ f)) hb
    rw [← Category.assoc, boundary.ι_ι, intervalMappingBoundary_face_zero,
      Equiv.apply_symm_apply, stdSimplex.yonedaEquiv_δ_comp] at h
    exact h

/-- 概要：端点を持つ実際の辺と、両端固定の区間模型の頂点は全単射に対応する。
方針：関手頂点と Yoneda の二つの全単射の往復を使う。
規約：型の全単射であり、同値類に落とす必要はない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、写像空間の比較射の全頂点での計算。 -/
noncomputable def intervalMappingEdgeVertexEquiv {X : SSet.{u}} (x y : X _⦋0⦌) :
    SSet.Edge x y ≃ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) _⦋0⦌ where
  toFun := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge
  invFun := intervalMappingEdgeOfVertex
  left_inv e := by
    apply SSet.Edge.ext
    change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] : SSet.{u}) X).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm e.edge))) = e.edge
    rw [show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm e.edge) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _ (SSet.yonedaEquiv.symm e.edge) from rfl,
      Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  right_inv v := by
    apply Subtype.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm (SSet.yonedaEquiv
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] : SSet.{u}) X).symm v.val))) = v.val
    rw [Equiv.symm_apply_apply]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply v.val

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
