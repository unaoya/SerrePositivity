module

public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FiniteLimitsColimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiniteShapes
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Pointed
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape

/-! # 安定 ∞ 圏

概要：安定性を零対象、全ての射の fiber/cofiber、零角の四角形の双方向の判定で定義する。
方針：HA Definition 1.1.1.9 の三条件を A2 の充填条件で表す。
規約：三角圏や Σ の可逆性を仮定に含めない。使われ方：h C の三角構造と D7 の安定性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial

/-- 概要：零対象、全射の fiber/cofiber、零角の列の一致を持つ quasicategory は安定である。
方針：HA 1.1.1.9 の三条件を実際の頂点・辺・四角形で表す。
規約：fiber/cofiber の選択は存在命題のみ。使われ方：ΣΩ と h C の三角構造の前提。 -/
class IsStable (X : SSet.{u}) [Quasicategory X] : Prop extends _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X where
  fiber_exists {x y : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) : Nonempty (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare f)
  cofiber_exists {x y : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) : Nonempty (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare f)
  fiber_iff_cofiber (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t ↔ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t

/-- 概要：安定な ∞ 圏の任意の射の fiber 四角形を選ぶ。
方針：存在条件から古典的選択を使う。
規約：関手性と選択の比較は S3 で別に証明する。使われ方：fiber の選択の入力。 -/
def chosenFiberSquare {X : SSet.{u}} [Quasicategory X] [IsStable X] {x y : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare f :=
  Classical.choice (IsStable.fiber_exists f)

/-- 概要：安定な ∞ 圏の任意の射の cofiber 四角形を選ぶ。
方針：存在条件から古典的選択を使う。
規約：関手性はまだ主張しない。使われ方：cofiber の選択の入力。 -/
def chosenCofiberSquare {X : SSet.{u}} [Quasicategory X] [IsStable X] {x y : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare f :=
  Classical.choice (IsStable.cofiber_exists f)

/-- 概要：安定な ∞ 圏の零角の引き戻し四角形は押し出しでもある。
方針：安定性の第三条件の順方向を使う。
規約：零角の条件を保持する。使われ方：cofiber 列から suspension を扱う際の双対性。 -/
lemma IsStable.pushout_of_pullback {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare t.square) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare t.square :=
  (IsStable.fiber_iff_cofiber t).1 ht

/-- 概要：安定な ∞ 圏の零角の押し出し四角形は引き戻しでもある。
方針：安定性の第三条件の逆方向を使う。
規約：一般の四角形への拡張は別に証明する。使われ方：fiber と cofiber の比較。 -/
lemma IsStable.pullback_of_pushout {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare t.square) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare t.square :=
  (IsStable.fiber_iff_cofiber t).2 ht

/-- 概要：有限極限・有限余極限を持ち、引き戻しと押し出しが一致する pointed ∞ 圏は安定である。
方針：二つの外側二次元ホーンの極限・余極限から fiber/cofiber を構成する。
規約：HA 1.1.3.4 の十分な向きのみであり、逆向きは入力しない。
使われ方：有限極限・余極限からの安定性の判定。 -/
theorem isStable_of_finite_limits_colimits {X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits X]
    (h : ∀ F : Δ[1] ⊗ Δ[1] ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F) : IsStable X where
  toHasZeroVertex := inferInstance
  fiber_exists f := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_fiberSquare_of_cospan_limits
    (fun p => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits.hasLimit p) f
  cofiber_exists f := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_cofiberSquare_of_span_colimits
    (fun p => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits.hasColimit p) f
  fiber_iff_cofiber t := h t.square

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
