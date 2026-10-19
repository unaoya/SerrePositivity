module
public import SerrePositivity.InfinityCategories.Stable.TrivialFibrationStability
public import SerrePositivity.InfinityCategories.Stable.TrivialFibrationSection

/-! # 自明 Kan fibration による安定性の降下

概要：安定な始域からの自明 Kan fibration の基底も安定である。
方針：厳密な切断で辺を持ち上げ、射影で普遍四角形を戻す。
規約：fiber/cofiber と零角の判定を実際の四角形で証明する。
使われ方：β3 の dg 模型間の安定性の同値不変性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
variable {E B : SSet.{u}} [Quasicategory E] [Quasicategory B]

/-- 安定な始域からの自明 Kan fibration の基底は安定。 -/
lemma isStable_target_of_trivialKanFibration (q : E ⟶ B) [TrivialKanFibration q]
    [IsStable E] : IsStable B := by
  obtain ⟨s, hs⟩ := trivialKanFibration_exists_section q
  refine {
    exists_zero := ?_
    fiber_exists := ?_
    cofiber_exists := ?_
    fiber_iff_cofiber := ?_ }
  · let z := chosenZeroVertex E
    exact ⟨q.app (Opposite.op ⦋0⦌) z.vertex,
      (isZeroVertex_iff_map_of_trivialKanFibration q z.vertex).1 z.isZero⟩
  · intro x y f
    let t := chosenFiberSquare (f.map ((truncation 2).map s))
    refine ⟨{
      square := t.square ≫ q
      zero_corner := (isZeroVertex_iff_map_of_trivialKanFibration q _).1 t.zero_corner
      right_edge := ?_
      isPullback := (isPullbackSquare_iff_postcomp_trivialKanFibration q _).1 t.isPullback }⟩
    rw [← Category.assoc, t.right_edge, SSet.yonedaEquiv_symm_comp]
    apply congrArg SSet.yonedaEquiv.symm
    exact ConcreteCategory.congr_hom
      (congrArg (fun h : B ⟶ B => h.app (Opposite.op ⦋1⦌)) hs) f.edge
  · intro x y f
    let t := chosenCofiberSquare (f.map ((truncation 2).map s))
    refine ⟨{
      square := t.square ≫ q
      zero_corner := (isZeroVertex_iff_map_of_trivialKanFibration q _).1 t.zero_corner
      bottom_edge := ?_
      isPushout := (isPushoutSquare_iff_postcomp_trivialKanFibration q _).1 t.isPushout }⟩
    rw [← Category.assoc, t.bottom_edge, SSet.yonedaEquiv_symm_comp]
    apply congrArg SSet.yonedaEquiv.symm
    exact ConcreteCategory.congr_hom
      (congrArg (fun h : B ⟶ B => h.app (Opposite.op ⦋1⦌)) hs) f.edge
  · intro t
    have hz : PreservesZeroVertices s := fun x hx =>
      (isZeroVertex_iff_map_section_of_trivialKanFibration q s hs x).1 hx
    change IsPullbackSquare t.square ↔ IsPushoutSquare t.square
    rw [isPullbackSquare_iff_postcomp_section_of_trivialKanFibration q s hs,
      isPushoutSquare_iff_postcomp_section_of_trivialKanFibration q s hs]
    exact IsStable.fiber_iff_cofiber (t.map s hz)

/-- 自明 Kan fibration の両端の安定性は同値。 -/
lemma isStable_iff_of_trivialKanFibration (q : E ⟶ B) [TrivialKanFibration q] :
    IsStable E ↔ IsStable B := by
  constructor
  · intro h
    let := h
    exact isStable_target_of_trivialKanFibration q
  · intro h
    let := h
    exact isStable_of_trivialKanFibration q

end SerrePositivity.InfinityCategories
