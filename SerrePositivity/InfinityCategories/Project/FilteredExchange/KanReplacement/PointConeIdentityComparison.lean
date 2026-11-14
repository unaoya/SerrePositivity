module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalMappingSpace
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalUniqueness
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SliceIdentityTerminal
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.PointConeDegeneracy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibrationInvertibleReflection

/-!
概要：一点図式の元の錐と恒等錐の間の比較は、底で元の脚そのもの。
方針：元の脚の終点を重ねた退化三角形を slice の辺にする。
規約：元の比較辺を保持。使われ方：指定脚の可逆性による一点極限錐の判定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 元の一点錐から恒等錐への指定された比較辺。 -/
def pointConeIdentityComparison {X : SSet.{u}} (x : X _⦋0⦌)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (SSet.yonedaEquiv.symm x)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm x)).Edge c (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone x) where
  edge := ⟨_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pointConeDegeneracy ≫ c.val, by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[1] : SSet.{u}) Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pointConeDegeneracy ≫ c.val) = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pointConeDegeneracy_inr, c.property]⟩
  src_eq := by
    apply Subtype.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 Δ[0]) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pointConeDegeneracy ≫ c.val) = c.val
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pointConeDegeneracy_face_one, Category.id_comp]
  tgt_eq := by
    apply Subtype.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 Δ[0]) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pointConeDegeneracy ≫ c.val) = SSet.const x
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pointConeDegeneracy_face_zero, SSet.const_comp]
    congr 1
    have h := congrArg SSet.yonedaEquiv c.property
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
    exact h

/-- 指定比較辺の底への像は、元の一点錐の脚の標準辺の表示。 -/
lemma pointConeIdentityComparison_projection_edge {X : SSet.{u}} (x : X _⦋0⦌)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (SSet.yonedaEquiv.symm x)) :
    ((pointConeIdentityComparison x c).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm x))).edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceOverVertexEdge x c).edge := by
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[1] Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pointConeDegeneracy ≫ c.val)) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pointConeDegeneracy_inl]
  rfl

/-- 元の一点錐が極限であることと、元の指定脚が可逆なことは同値。 -/
lemma isLimitCone_point_iff_invertible {X : SSet.{u}} [Quasicategory X]
    (x : X _⦋0⦌) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (SSet.yonedaEquiv.symm x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceOverVertexEdge x c) := by
  let e := pointConeIdentityComparison x c
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceIdentityCone_isTerminalVertex x
  constructor
  · intro hc
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e.toTruncated :=
      isIso_of_isTerminal hc.isTerminalHo hd.isTerminalHo _
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (pointConeIdentityComparison_projection_edge x c)).mp
      (he.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm x)))
  · intro hc
    have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm x))) :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (pointConeIdentityComparison_projection_edge x c)).mpr hc
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightFibration_reflects_isInvertibleEdge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm x)) e hp
    have : IsIso (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) := he
    exact hd.of_vertexIso (asIso (SSet.Truncated.HomotopyCategory.homMk e.toTruncated)).symm

/-- 一点図式の任意の表示でも、元の標準脚の可逆性が極限性を判定する。 -/
lemma isLimitCone_point_iff_edge {X : SSet.{u}} [Quasicategory X]
    {p : (Δ[0] : SSet.{u}) ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      (SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ c.val))) := by
  obtain ⟨x, rfl⟩ := SSet.yonedaEquiv.symm.surjective p
  exact (isLimitCone_point_iff_invertible x c).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (rfl : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceOverVertexEdge x c).edge = _))

end SerrePositivity.InfinityCategories.Project.FilteredExchange
