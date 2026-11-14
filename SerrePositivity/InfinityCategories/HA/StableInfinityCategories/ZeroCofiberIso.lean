module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.ZeroTargetProduct
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialTransport

/-! # 零 fiber・零 cofiber による射の同型判定

概要：安定 ∞ 圏では cofiber または fiber が零である射は h C の同型となる。
方針：零角の安定性と、終対象因子の二項積・始対象因子の二項余積を使う。
規約：前加法構造や三角構造は不要。使われ方：余積と積の比較、完全列、三角形の同型判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：左側二頂点が始対象である押し出しの右辺は h C の同型。
方針：始対象を第二因子とする二項余積の第一包含の同型性を使う。
規約：値域は quasicategory、安定性は不要。使われ方：零 fiber の射の同型判定。 -/
lemma isIso_squareHoRight_of_pushout_initial_left {X : SSet.{u}} [Quasicategory X]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex R 0 0))
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex R 0 1)) : IsIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight R) :=
  (BinaryCofan.isColimit_iff_isIso_inl h₁.isInitialHo
    (BinaryCofan.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight R) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoTop R))).1
      ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourcePushout_isBinaryCoproduct R hR h₀⟩

/-- 概要：終端頂点が終対象である fiber 列の第一射は同型。
方針：零角と終端頂点を終対象因子の二項積として扱う。
規約：任意の零射構造で成り立ち、安定性は不要。使われ方：零 cofiber の場合への適用。 -/
lemma ZeroTriangle.isIso_f_of_fiber_terminal_cofiber {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsFiberSequence t)
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 1)) : IsIso t.hoShortComplex.f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isIso_squareHoBottom_of_pullback_terminal_top t.square ht t.zero_corner.2 hz

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangle (isIso_f_of_fiber_terminal_cofiber)


/-- 概要：始点が始対象である cofiber 列の第二射は同型。
方針：零角と始点を始対象因子の二項余積として扱う。
規約：任意の零射構造で成り立ち、安定性は不要。使われ方：零 fiber の場合への適用。 -/
lemma ZeroTriangle.isIso_g_of_cofiber_initial_fiber {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence t)
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 0 0)) : IsIso t.hoShortComplex.g :=
  isIso_squareHoRight_of_pushout_initial_left t.square ht hz t.zero_corner.1

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangle (isIso_g_of_cofiber_initial_fiber)


/-- 概要：安定な場合、終端頂点が零の cofiber 列の第一射は同型。
方針：cofiber 列を fiber 列として扱い、終対象終点の判定を使う。
規約：前加法構造は不要。使われ方：cofiber の消滅からの同型判定。 -/
lemma ZeroTriangle.isIso_f_of_zero_cofiber {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence t)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 1)) : IsIso t.hoShortComplex.f :=
  t.isIso_f_of_fiber_terminal_cofiber ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.fiber_iff_cofiber t).2 ht) hz.2

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangle (isIso_f_of_zero_cofiber)


/-- 概要：安定な場合、始点が零の fiber 列の第二射は同型。
方針：fiber 列を cofiber 列として扱い、始対象始点の判定を使う。
規約：前加法構造は不要。使われ方：fiber の消滅からの同型判定。 -/
lemma ZeroTriangle.isIso_g_of_zero_fiber {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsFiberSequence t)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 0 0)) : IsIso t.hoShortComplex.g :=
  t.isIso_g_of_cofiber_initial_fiber ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.fiber_iff_cofiber t).1 ht) hz.1

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangle (isIso_g_of_zero_fiber)


/-- 概要：指定した辺の cofiber が零なら、その辺の類は同型。
方針：cofiber 列の第一射の判定を指定辺との Arrow の等号で移す。
規約：任意の cofiber 四角形の選択で成り立つ。使われ方：元の射の同型の認証。 -/
lemma CofiberSquare.homMk_isIso_of_zero {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {x y : X _⦋0⦌} {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare f) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex s.cofiber) :
    IsIso (SSet.Truncated.HomotopyCategory.homMk f) := by
  have hi := s.toZeroTriangle.isIso_f_of_zero_cofiber s.isPushout hz
  change IsIso (Arrow.mk (SSet.Truncated.HomotopyCategory.homMk f)).hom
  rw [← s.hoShortComplex_f_arrow]
  exact hi

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberSquare (homMk_isIso_of_zero)


/-- 概要：指定した辺の fiber が零なら、その辺の類は同型。
方針：fiber 列の第二射の判定を指定辺との Arrow の等号で移す。
規約：任意の fiber 四角形の選択で成り立つ。使われ方：元の射の同型の認証。 -/
lemma FiberSquare.homMk_isIso_of_zero {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {x y : X _⦋0⦌} {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare f) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex s.fiber) :
    IsIso (SSet.Truncated.HomotopyCategory.homMk f) := by
  have hi := s.toZeroTriangle.isIso_g_of_zero_fiber s.isPullback hz
  change IsIso (Arrow.mk (SSet.Truncated.HomotopyCategory.homMk f)).hom
  rw [← s.hoShortComplex_g_arrow]
  exact hi

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FiberSquare (homMk_isIso_of_zero)


end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
