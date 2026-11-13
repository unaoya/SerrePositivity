module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroCofiberIso

/-! # fiber・cofiber 列の三対象の消滅

概要：安定 ∞ 圏の fiber/cofiber 列で三対象のうち二つが零なら残りも零である。
方針：零 fiber・零 cofiber の同型判定を使い、零頂点を同型で移す。
規約：加法構造や三角圏の公理は不要。使われ方：比較射の cofiber による同型判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：cofiber 列の第一・第二対象が零なら第三対象も零。
方針：第一対象の零性で第二射を同型とし、第二対象の零性を移す。
規約：値域は安定な quasicategory。使われ方：二つの零対象の cofiber の消滅。 -/
lemma ZeroTriangle.zero_cofiber_of_zero_source_middle {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence t)
    (h₀ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 0 0))
    (h₁ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 0)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 1) := by
  let := t.isIso_g_of_cofiber_initial_fiber ht h₀.1
  exact h₁.of_vertexIso (asIso t.hoShortComplex.g)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangle (zero_cofiber_of_zero_source_middle)


/-- 概要：cofiber 列の第一・第三対象が零なら第二対象も零。
方針：第一対象の零性で第二射を同型とし、第三対象から逆向きに零性を移す。
規約：値域は安定な quasicategory。使われ方：比較列の中間対象の消滅。 -/
lemma ZeroTriangle.zero_middle_of_zero_source_cofiber {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence t)
    (h₀ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 0 0))
    (h₂ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 0) := by
  let := t.isIso_g_of_cofiber_initial_fiber ht h₀.1
  exact h₂.of_vertexIso (asIso t.hoShortComplex.g).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangle (zero_middle_of_zero_source_cofiber)


/-- 概要：cofiber 列の第二・第三対象が零なら第一対象も零。
方針：第三対象の零性で第一射を同型とし、第二対象から逆向きに零性を移す。
規約：値域は安定な quasicategory。使われ方：比較列の第一対象の消滅。 -/
lemma ZeroTriangle.zero_source_of_zero_middle_cofiber {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence t)
    (h₁ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 0))
    (h₂ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 0 0) := by
  let := t.isIso_f_of_zero_cofiber ht h₂
  exact h₁.of_vertexIso (asIso t.hoShortComplex.f).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangle (zero_source_of_zero_middle_cofiber)


/-- 概要：fiber 列の第一・第二対象が零なら第三対象も零。
方針：安定性で cofiber 列へ移す。
規約：前加法構造は不要。使われ方：fiber による消滅判定。 -/
lemma ZeroTriangle.zero_cofiber_of_fiber_zero_source_middle {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsFiberSequence t)
    (h₀ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 0 0))
    (h₁ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 0)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 1) :=
  t.zero_cofiber_of_zero_source_middle ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.fiber_iff_cofiber t).1 ht) h₀ h₁

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangle (zero_cofiber_of_fiber_zero_source_middle)


/-- 概要：fiber 列の第一・第三対象が零なら第二対象も零。
方針：安定性で cofiber 列へ移す。
規約：前加法構造は不要。使われ方：fiber による消滅判定。 -/
lemma ZeroTriangle.zero_middle_of_fiber_zero_source_cofiber {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsFiberSequence t)
    (h₀ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 0 0))
    (h₂ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 0) :=
  t.zero_middle_of_zero_source_cofiber ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.fiber_iff_cofiber t).1 ht) h₀ h₂

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangle (zero_middle_of_fiber_zero_source_cofiber)


/-- 概要：fiber 列の第二・第三対象が零なら第一対象も零。
方針：安定性で cofiber 列へ移す。
規約：前加法構造は不要。使われ方：fiber による消滅判定。 -/
lemma ZeroTriangle.zero_source_of_fiber_zero_middle_cofiber {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsFiberSequence t)
    (h₁ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 0))
    (h₂ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 0 0) :=
  t.zero_source_of_zero_middle_cofiber ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.fiber_iff_cofiber t).1 ht) h₁ h₂

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangle (zero_source_of_fiber_zero_middle_cofiber)


end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
