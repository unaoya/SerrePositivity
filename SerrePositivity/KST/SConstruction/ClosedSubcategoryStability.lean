module
public import SerrePositivity.KST.SConstruction.SquareBoundaryVertices

/-! # 閉性からの全部分圏の安定性
概要：零対象・押し出し・引き戻しの閉性から全部分圏の安定性と包含の完全性を導く。
方針：指定辺の普遍四角形を全頂点の閉性で持ち上げ、零角の双方向の普遍性を反映する。
規約：安定性を入力の構造体に仮定しない。使われ方：相対 E(A,C,B) の安定な模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 全部分圏の指定辺の周囲での cofiber 四角形は内部へ持ち上がる。 -/
lemma closedSubcategory_cofiber_nonempty {X : StableModel.{u}} (P : ClosedStablePredicate X)
    {x y : (closedSubcategory P) _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj (closedSubcategory P)) x y) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare f) := by
  let i := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ P.predicate).ι
  let e := f.map ((truncation 2).map i)
  let t := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare e
  have hc := square_bottom_vertices e t.square t.bottom_edge
  have h00 : P.predicate (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 0 0) := hc.1.symm ▸ closedSubcategory_vertex P x
  have h10 : P.predicate (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 0) := hc.2.symm ▸ closedSubcategory_vertex P y
  have h01 := P.zero_mem t.zero_corner
  have hv := square_vertices_of_corners P.predicate t.square h00 h10 h01
    (P.pushout_mem t.square t.isPushout h00 h10 h01)
  let D := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift P.predicate t.square hv
  have hDi : D ≫ i = t.square := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
  have hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex D 0 1).val := by
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (D ≫ i) 0 1)
    rw [hDi]
    exact t.zero_corner
  refine ⟨{
    square := D
    zero_corner := ⟨isInitialVertex_fullSubcomplex_of_ambient P.predicate _ hz.1,
      isTerminalVertex_fullSubcomplex_of_ambient P.predicate _ hz.2⟩
    bottom_edge := ?_
    isPushout := isPushoutSquare_fullSubcomplex_of_ambient P.predicate D (hDi.symm ▸ t.isPushout) }⟩
  apply (cancel_mono i).1
  rw [Category.assoc, hDi]
  exact t.bottom_edge.trans (SSet.yonedaEquiv_symm_comp f.edge i).symm

/-- 全部分圏の指定辺の周囲での fiber 四角形も内部へ持ち上がる。 -/
lemma closedSubcategory_fiber_nonempty {X : StableModel.{u}} (P : ClosedStablePredicate X)
    {x y : (closedSubcategory P) _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj (closedSubcategory P)) x y) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare f) := by
  let i := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ P.predicate).ι
  let e := f.map ((truncation 2).map i)
  let t := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenFiberSquare e
  have hc := square_right_vertices e t.square t.right_edge
  have h10 : P.predicate (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 0) := hc.1.symm ▸ closedSubcategory_vertex P x
  have h11 : P.predicate (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 1) := hc.2.symm ▸ closedSubcategory_vertex P y
  have h01 := P.zero_mem t.zero_corner
  have hv := square_vertices_of_corners P.predicate t.square
    (P.pullback_mem t.square t.isPullback h10 h01 h11) h10 h01 h11
  let D := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift P.predicate t.square hv
  have hDi : D ≫ i = t.square := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
  have hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex D 0 1).val := by
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (D ≫ i) 0 1)
    rw [hDi]
    exact t.zero_corner
  refine ⟨{
    square := D
    zero_corner := ⟨isInitialVertex_fullSubcomplex_of_ambient P.predicate _ hz.1,
      isTerminalVertex_fullSubcomplex_of_ambient P.predicate _ hz.2⟩
    right_edge := ?_
    isPullback := isPullbackSquare_fullSubcomplex_of_ambient P.predicate D
      (hDi.symm ▸ t.isPullback) }⟩
  apply (cancel_mono i).1
  rw [Category.assoc, hDi]
  exact t.right_edge.trans (SSet.yonedaEquiv_symm_comp f.edge i).symm

/-- 周囲の零対象と押し出し・引き戻しに閉じた全部分圏は安定。 -/
instance closedSubcategory_isStable {X : StableModel.{u}} (P : ClosedStablePredicate X) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (closedSubcategory P) where
  toHasZeroVertex := inferInstance
  fiber_exists := closedSubcategory_fiber_nonempty P
  cofiber_exists := closedSubcategory_cofiber_nonempty P
  fiber_iff_cofiber t := by
    let i := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ P.predicate).ι
    let T : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X.carrier := ⟨t.square ≫ i,
      closedSubcategoryInclusion_preservesZero P _ t.zero_corner⟩
    constructor
    · intro ht
      apply isPushoutSquare_fullSubcomplex_of_ambient P.predicate
      exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pushout_of_pullback T (closedSubcategoryInclusion_preservesFiber P t ht)
    · intro ht
      apply isPullbackSquare_fullSubcomplex_of_ambient P.predicate
      exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pullback_of_pushout T
        (closedSubcategoryInclusion_preservesPushout P t.square ht)

/-- 閉じた全部分圏を安定な入力の模型として束ねる。 -/
def closedStableModel {X : StableModel.{u}} (P : ClosedStablePredicate X) : StableModel.{u} :=
  ⟨closedSubcategory P⟩

/-- 閉じた全部分圏の包含は完全関手を与える。 -/
def closedStableInclusion {X : StableModel.{u}} (P : ClosedStablePredicate X) :
    closedStableModel P ⟶ X :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ P.predicate).ι,
    (closedSubcategoryInclusion_preservesSConstructionData P).toCofiberData⟩

end SerrePositivity.KST.SConstruction
