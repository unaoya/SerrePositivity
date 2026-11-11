module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TrivialFibrationSquares

/-! # 自明 Kan fibration に沿う安定性の反映

概要：安定な基底への自明 Kan fibration の始域は安定である。
方針：与えられた辺を厳密に保って fiber/cofiber 四角形を持ち上げる。
規約：安定性の定義の三条件を実際の零頂点と四角形で検証する。
使われ方：β3 の表現可能 dg 模型と分解の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial

/-- 正方形の右辺の包含は単射。 -/
instance mono_squareRightEdge : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge.{u}) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro a b h
  exact congrArg Prod.snd h

/-- 正方形の下辺の包含は単射。 -/
instance mono_squareBottomEdge : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge.{u}) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro a b h
  exact congrArg Prod.fst h

variable {E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
variable (q : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q]

/-- 基底の fiber 四角形を元の辺を固定して持ち上げる。 -/
lemma trivialKanFibration_lift_fiberSquare {x y : E _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj E) x y)
    (s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare (f.map ((truncation 2).map q))) : Nonempty (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare f) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := q) _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge inferInstance
  have sq : CommSq (SSet.yonedaEquiv.symm f.edge) _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge q s.square := ⟨by
    rw [s.right_edge, SSet.yonedaEquiv_symm_comp]
    rfl⟩
  refine ⟨{
    square := sq.lift
    zero_corner := ?_
    right_edge := sq.fac_left
    isPullback := ?_ }⟩
  · apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isZeroVertex_iff_map_of_trivialKanFibration q _).2
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (sq.lift ≫ q) 0 1)
    rw [sq.fac_right]
    exact s.zero_corner
  · apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPullbackSquare_iff_postcomp_trivialKanFibration q _).2
    rw [sq.fac_right]
    exact s.isPullback

/-- 基底の cofiber 四角形を元の辺を固定して持ち上げる。 -/
lemma trivialKanFibration_lift_cofiberSquare {x y : E _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj E) x y)
    (s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare (f.map ((truncation 2).map q))) : Nonempty (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare f) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := q) _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge inferInstance
  have sq : CommSq (SSet.yonedaEquiv.symm f.edge) _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge q s.square := ⟨by
    rw [s.bottom_edge, SSet.yonedaEquiv_symm_comp]
    rfl⟩
  refine ⟨{
    square := sq.lift
    zero_corner := ?_
    bottom_edge := sq.fac_left
    isPushout := ?_ }⟩
  · apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isZeroVertex_iff_map_of_trivialKanFibration q _).2
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (sq.lift ≫ q) 0 1)
    rw [sq.fac_right]
    exact s.zero_corner
  · apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPushoutSquare_iff_postcomp_trivialKanFibration q _).2
    rw [sq.fac_right]
    exact s.isPushout

/-- 安定な基底への自明 Kan fibration の始域は安定。 -/
lemma isStable_of_trivialKanFibration (q : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q]
    [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable B] : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable E where
  exists_zero := by
    obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section q
    let z := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex B
    refine ⟨s.app (Opposite.op ⦋0⦌) z.vertex,
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isZeroVertex_iff_map_of_trivialKanFibration q _).2 ?_⟩
    have h := ConcreteCategory.congr_hom
      (congrArg (fun f : B ⟶ B => f.app (Opposite.op ⦋0⦌)) hs) z.vertex
    change q.app (Opposite.op ⦋0⦌) (s.app (Opposite.op ⦋0⦌) z.vertex) = z.vertex at h
    rw [h]
    exact z.isZero
  fiber_exists f := trivialKanFibration_lift_fiberSquare q f
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenFiberSquare (f.map ((truncation 2).map q)))
  cofiber_exists f := trivialKanFibration_lift_cofiberSquare q f
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare (f.map ((truncation 2).map q)))
  fiber_iff_cofiber t := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare t.square ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare t.square
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPullbackSquare_iff_postcomp_trivialKanFibration q,
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPushoutSquare_iff_postcomp_trivialKanFibration q]
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.fiber_iff_cofiber (t.map q (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.trivialKanFibration_preservesZeroVertices q))

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
