module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IntervalSquareComposition
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalUniversalPrism

/-!
概要：元の四角形の底辺の普遍 prism を固定した、実際の全持ち上げを保持する。
方針：元の transportIso と同じ底辺からの持ち上げを構造体へ束ねる。
規約：元の選択済み普遍輸送を保持。使われ方：指定合成比較の持ち上げ表示と選択照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B P : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  {a b c d : B _⦋0⦌} (s : TransportIntervalSquare P a b c d)
  (f : P ⟶ vertexFiber p a)

/-- 元の底辺の普遍 prism を厳密に固定する、同じ全四角形の持ち上げ。 -/
structure TransportSquareLift where
  /-- 元の二時間・全パラメータを持つ実四角形。 -/
  square : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ P) ⟶ E
  /-- 底辺は元の同じ普遍 prism。 -/
  zero : prismEndpoint 0 _ ≫ square = diagonalUniversalPrism p f s.bottom
  /-- 元の底の四角形を被覆する。 -/
  over_base : square ≫ p = s.square

/-- 元の transportIso と同じ持ち上げの選択を、その実四角形として保持する。 -/
def transportSquareCanonicalLift : TransportSquareLift p s f := by
  let h := leftFibration_lift_prism p (diagonalUniversalPrism p f s.bottom) s.square
    ((diagonalUniversalPrism_projection p f s.bottom).trans s.zero.symm)
  exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2⟩

variable {p s f} (L : TransportSquareLift p s f)

/-- 同じ持ち上げの上辺の実 prism。 -/
def TransportSquareLift.top : (Δ[1] : SSet.{u}) ⊗ P ⟶ E :=
  prismEndpoint 1 _ ≫ L.square

/-- 同じ持ち上げの左辺の実 prism。 -/
def TransportSquareLift.left : (Δ[1] : SSet.{u}) ⊗ P ⟶ E :=
  (Δ[1] ◁ prismEndpoint 0 P) ≫ L.square

/-- 同じ持ち上げの右辺の実 prism。 -/
def TransportSquareLift.right : (Δ[1] : SSet.{u}) ⊗ P ⟶ E :=
  (Δ[1] ◁ prismEndpoint 1 P) ≫ L.square

/-- 上辺も元の同じ区間族を厳密に被覆する。 -/
lemma TransportSquareLift.top_projection : L.top ≫ p = intervalMappingUncurry s.top := by
  rw [TransportSquareLift.top, Category.assoc, L.over_base, s.one]

/-- 左辺も元の同じ区間族を厳密に被覆する。 -/
lemma TransportSquareLift.left_projection : L.left ≫ p = intervalMappingUncurry s.left := by
  rw [TransportSquareLift.left, Category.assoc, L.over_base, s.inner_zero]

/-- 右辺も元の同じ区間族を厳密に被覆する。 -/
lemma TransportSquareLift.right_projection : L.right ≫ p = intervalMappingUncurry s.right := by
  rw [TransportSquareLift.right, Category.assoc, L.over_base, s.inner_one]

end SerrePositivity.InfinityCategories.F2
