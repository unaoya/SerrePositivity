module
public import SerrePositivity.InfinityCategories.Stable.TrivialFibrationSquares

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

/-- 正方形の右辺の包含は単射。 -/
instance mono_squareRightEdge : Mono (squareRightEdge.{u}) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro a b h
  exact congrArg Prod.snd h

/-- 正方形の下辺の包含は単射。 -/
instance mono_squareBottomEdge : Mono (squareBottomEdge.{u}) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro a b h
  exact congrArg Prod.fst h

variable {E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
variable (q : E ⟶ B) [TrivialKanFibration q]

/-- 基底の fiber 四角形を元の辺を固定して持ち上げる。 -/
lemma trivialKanFibration_lift_fiberSquare {x y : E _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj E) x y)
    (s : FiberSquare (f.map ((truncation 2).map q))) : Nonempty (FiberSquare f) := by
  have := TrivialKanFibration.mem (p := q) squareRightEdge inferInstance
  have sq : CommSq (SSet.yonedaEquiv.symm f.edge) squareRightEdge q s.square := ⟨by
    rw [s.right_edge, SSet.yonedaEquiv_symm_comp]
    rfl⟩
  refine ⟨{
    square := sq.lift
    zero_corner := ?_
    right_edge := sq.fac_left
    isPullback := ?_ }⟩
  · apply (isZeroVertex_iff_map_of_trivialKanFibration q _).2
    change IsZeroVertex (squareVertex (sq.lift ≫ q) 0 1)
    rw [sq.fac_right]
    exact s.zero_corner
  · apply (isPullbackSquare_iff_postcomp_trivialKanFibration q _).2
    rw [sq.fac_right]
    exact s.isPullback

/-- 基底の cofiber 四角形を元の辺を固定して持ち上げる。 -/
lemma trivialKanFibration_lift_cofiberSquare {x y : E _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj E) x y)
    (s : CofiberSquare (f.map ((truncation 2).map q))) : Nonempty (CofiberSquare f) := by
  have := TrivialKanFibration.mem (p := q) squareBottomEdge inferInstance
  have sq : CommSq (SSet.yonedaEquiv.symm f.edge) squareBottomEdge q s.square := ⟨by
    rw [s.bottom_edge, SSet.yonedaEquiv_symm_comp]
    rfl⟩
  refine ⟨{
    square := sq.lift
    zero_corner := ?_
    bottom_edge := sq.fac_left
    isPushout := ?_ }⟩
  · apply (isZeroVertex_iff_map_of_trivialKanFibration q _).2
    change IsZeroVertex (squareVertex (sq.lift ≫ q) 0 1)
    rw [sq.fac_right]
    exact s.zero_corner
  · apply (isPushoutSquare_iff_postcomp_trivialKanFibration q _).2
    rw [sq.fac_right]
    exact s.isPushout

/-- 安定な基底への自明 Kan fibration の始域は安定。 -/
lemma isStable_of_trivialKanFibration (q : E ⟶ B) [TrivialKanFibration q]
    [IsStable B] : IsStable E where
  exists_zero := by
    obtain ⟨s, hs⟩ := trivialKanFibration_exists_section q
    let z := chosenZeroVertex B
    refine ⟨s.app (Opposite.op ⦋0⦌) z.vertex,
      (isZeroVertex_iff_map_of_trivialKanFibration q _).2 ?_⟩
    have h := ConcreteCategory.congr_hom
      (congrArg (fun f : B ⟶ B => f.app (Opposite.op ⦋0⦌)) hs) z.vertex
    change q.app (Opposite.op ⦋0⦌) (s.app (Opposite.op ⦋0⦌) z.vertex) = z.vertex at h
    rw [h]
    exact z.isZero
  fiber_exists f := trivialKanFibration_lift_fiberSquare q f
    (chosenFiberSquare (f.map ((truncation 2).map q)))
  cofiber_exists f := trivialKanFibration_lift_cofiberSquare q f
    (chosenCofiberSquare (f.map ((truncation 2).map q)))
  fiber_iff_cofiber t := by
    change IsPullbackSquare t.square ↔ IsPushoutSquare t.square
    rw [isPullbackSquare_iff_postcomp_trivialKanFibration q,
      isPushoutSquare_iff_postcomp_trivialKanFibration q]
    exact IsStable.fiber_iff_cofiber (t.map q (trivialKanFibration_preservesZeroVertices q))

end SerrePositivity.InfinityCategories
