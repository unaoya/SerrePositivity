module
public import SerrePositivity.InfinityCategories.Stable.Pointed
public import SerrePositivity.InfinityCategories.Stable.FiniteShapes
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite

/-! # 安定 ∞ 圏

概要：安定性を零対象、全ての射の fiber/cofiber、零角の四角形の双方向の判定で定義する。
方針：HA Definition 1.1.1.9 の三条件を A2 の充填条件で表す。
規約：三角圏や Σ の可逆性を仮定に含めない。使われ方：h C の三角構造と D7 の安定性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

/-- 概要：全ての有限単体集合の図式が極限を持つ。
方針：有限形状の図式に A2 の HasLimit を課す。
規約：形状と対象は同じ単体集合の宇宙。使われ方：HA Proposition 1.1.3.4 の十分条件。 -/
class HasFiniteLimits (X : SSet.{u}) : Prop where
  hasLimit {K : SSet.{u}} [K.Finite] (p : K ⟶ X) : HasLimit p

/-- 概要：全ての有限単体集合の図式が余極限を持つ。
方針：有限形状の図式に coslice による HasColimit を課す。
規約：形状と対象は同じ宇宙。使われ方：HA Proposition 1.1.3.4 の十分条件。 -/
class HasFiniteColimits (X : SSet.{u}) : Prop where
  hasColimit {K : SSet.{u}} [K.Finite] (p : K ⟶ X) : HasColimit p

/-- 概要：零対象、全射の fiber/cofiber、零角の列の一致を持つ quasicategory は安定である。
方針：HA 1.1.1.9 の三条件を実際の頂点・辺・四角形で表す。
規約：fiber/cofiber の選択は存在命題のみ。使われ方：ΣΩ と h C の三角構造の前提。 -/
class IsStable (X : SSet.{u}) [Quasicategory X] : Prop extends HasZeroVertex X where
  fiber_exists {x y : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) : Nonempty (FiberSquare f)
  cofiber_exists {x y : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) : Nonempty (CofiberSquare f)
  fiber_iff_cofiber (t : ZeroTriangle X) : IsFiberSequence t ↔ IsCofiberSequence t

/-- 概要：安定な ∞ 圏の任意の射の fiber 四角形を選ぶ。
方針：存在条件から古典的選択を使う。
規約：関手性と選択の比較は S3 で別に証明する。使われ方：fiber の選択の入力。 -/
def chosenFiberSquare {X : SSet.{u}} [Quasicategory X] [IsStable X] {x y : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) : FiberSquare f :=
  Classical.choice (IsStable.fiber_exists f)

/-- 概要：安定な ∞ 圏の任意の射の cofiber 四角形を選ぶ。
方針：存在条件から古典的選択を使う。
規約：関手性はまだ主張しない。使われ方：cofiber の選択の入力。 -/
def chosenCofiberSquare {X : SSet.{u}} [Quasicategory X] [IsStable X] {x y : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) : CofiberSquare f :=
  Classical.choice (IsStable.cofiber_exists f)

/-- 概要：安定な ∞ 圏の零角の引き戻し四角形は押し出しでもある。
方針：安定性の第三条件の順方向を使う。
規約：零角の条件を保持する。使われ方：cofiber 列から suspension を扱う際の双対性。 -/
lemma IsStable.pushout_of_pullback {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (t : ZeroTriangle X) (ht : IsPullbackSquare t.square) : IsPushoutSquare t.square :=
  (IsStable.fiber_iff_cofiber t).1 ht

/-- 概要：安定な ∞ 圏の零角の押し出し四角形は引き戻しでもある。
方針：安定性の第三条件の逆方向を使う。
規約：一般の四角形への拡張は別に証明する。使われ方：fiber と cofiber の比較。 -/
lemma IsStable.pullback_of_pushout {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (t : ZeroTriangle X) (ht : IsPushoutSquare t.square) : IsPullbackSquare t.square :=
  (IsStable.fiber_iff_cofiber t).2 ht

/-- 概要：有限極限・有限余極限を持ち、引き戻しと押し出しが一致する pointed ∞ 圏は安定である。
方針：二つの外側二次元ホーンの極限・余極限から fiber/cofiber を構成する。
規約：HA 1.1.3.4 の十分な向きのみであり、逆向きは入力しない。
使われ方：有限極限・余極限からの安定性の判定。 -/
theorem isStable_of_finite_limits_colimits {X : SSet.{u}} [Quasicategory X]
    [HasZeroVertex X] [HasFiniteLimits X] [HasFiniteColimits X]
    (h : ∀ F : Δ[1] ⊗ Δ[1] ⟶ X, IsPullbackSquare F ↔ IsPushoutSquare F) : IsStable X where
  toHasZeroVertex := inferInstance
  fiber_exists f := exists_fiberSquare_of_cospan_limits
    (fun p => HasFiniteLimits.hasLimit p) f
  cofiber_exists f := exists_cofiberSquare_of_span_colimits
    (fun p => HasFiniteColimits.hasColimit p) f
  fiber_iff_cofiber t := h t.square

end SerrePositivity.InfinityCategories
