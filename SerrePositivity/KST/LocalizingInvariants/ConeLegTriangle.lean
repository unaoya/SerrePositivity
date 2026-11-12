module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofSliceTriangle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.NativeConeLeg
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SliceProjectionLaws

/-!
概要：同じ実錐比較辺の頂点成分と各実脚を、一つの指定合成二単体で結ぶ。
方針：元の slice 辺を図式の同じ頂点へ制限し、点上の実 slice 三角形を読む。
規約：錐・比較辺・図式頂点と全二単体を選び直さない。
使われ方：零次商比較の有限錐回収で、実右分数と全脚の弱同値性を接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma coneRestrictionPoint_leg {K X : SSet.{u}} {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (k : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge (SSet.yonedaEquiv.symm k ≫ p)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict p (SSet.yonedaEquiv.symm k)).app (Opposite.op ⦋0⦌) c)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c k).edge := by
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (SSet.yonedaEquiv.symm k) ≫ c.val)) =
    c.val.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneLegInclusion k))
  rw [← SSet.yonedaEquiv_comp]
  rfl

/-- 元の錐比較の頂点射と各脚の合成を、同じ実二単体で厳密に回収する。 -/
def coneLegComparisonTriangle {K X : SSet.{u}} {p : K ⟶ X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p}
    (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)) c d) (k : K _⦋0⦌) :
    Truncated.Edge.CompStruct (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg d k) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c k) := by
  let R := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict p (SSet.yonedaEquiv.symm k)
  let a := SSet.yonedaEquiv.symm k ≫ p
  let σ := R.app (Opposite.op ⦋1⦌) e.edge
  let t := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a σ
  refine { simplex := SSet.yonedaEquiv t, d₀ := ?_, d₁ := ?_, d₂ := ?_ }
  · change X.δ (2 : Fin 3) (SSet.yonedaEquiv t) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    change SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a σ) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_base]
    change ((R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection a).app (Opposite.op ⦋1⦌) e.edge) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverRestrict_projection]
    rfl
  · change X.δ (0 : Fin 3) (SSet.yonedaEquiv t) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    change SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a σ) = _
    have hl := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_leg a σ (0 : Fin 2)
    change SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a σ) = _ at hl
    rw [hl]
    change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).δ 0 (R.app (Opposite.op ⦋1⦌) e.edge))).edge = _
    have hn := R.naturality_apply (SimplexCategory.δ (0 : Fin 2)).op e.edge
    change R.app (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p).δ 0 e.edge) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).δ 0 (R.app (Opposite.op ⦋1⦌) e.edge) at hn
    rw [← hn]
    change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a (R.app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p).δ 0 e.edge))).edge = _
    have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p).δ 0 e.edge = d := e.tgt_eq
    rw [he]
    exact coneRestrictionPoint_leg d k
  · change X.δ (1 : Fin 3) (SSet.yonedaEquiv t) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    change SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a σ) = _
    have hl := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_leg a σ (1 : Fin 2)
    change SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a σ) = _ at hl
    rw [hl]
    change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).δ 1 (R.app (Opposite.op ⦋1⦌) e.edge))).edge = _
    have hn := R.naturality_apply (SimplexCategory.δ (1 : Fin 2)).op e.edge
    change R.app (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p).δ 1 e.edge) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).δ 1 (R.app (Opposite.op ⦋1⦌) e.edge) at hn
    rw [← hn]
    change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a (R.app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p).δ 1 e.edge))).edge = _
    have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p).δ 1 e.edge = c := e.src_eq
    rw [he]
    exact coneRestrictionPoint_leg c k

end SerrePositivity.KST.LocalizingInvariants
