module

public import SerrePositivity.KST.LocalizingInvariants.RelativeInvariant
public import SerrePositivity.KST.LocalizingInvariants.NativeFiberSequence

/-!
概要：提示つき相対 Verdier 四角形の、元の E 値の全整数長完全列。
方針：同じ実 fiber 四角形の両辺と整数 π 関手をそのまま使う。
規約：S 内の図式だけを評価する。使われ方：相対 Tamme fiber 列と pro 版。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.IsRelativeLocalizingInvariant
variable {S : SSet.{u + 1}} {ν : S ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}} {E : S ⟶ Sp.{u}}
  (hE : IsRelativeLocalizingInvariant ν E) (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram ν)

/-- 同じ E 像の三頂点の整数 π 群。 -/
abbrev group (i k : Fin 2) (j : ℤ) := NativeFiber.group (hE.fiberTriangle d) i k j

/-- S 内の包含辺の E 像の作用。 -/
def inclusion (j : ℤ) : hE.group d 0 0 j →* hE.group d 1 0 j :=
  NativeFiber.bottom (hE.fiberTriangle d) j

/-- S 内の商辺の E 像の作用。 -/
def projection (j : ℤ) : hE.group d 1 0 j →* hE.group d 1 1 j :=
  NativeFiber.right (hE.fiberTriangle d) j

/-- 元の E 像の fiber 四角形の接続射。 -/
def connecting (j : ℤ) : hE.group d 1 1 (j + 1) →* hE.group d 0 0 j :=
  NativeFiber.boundary (hE.fiberTriangle d) (hE.fiberTriangle_isFiber d) j

lemma exact_left (j : ℤ) (x : hE.group d 0 0 j) :
    hE.inclusion d j x = 1 ↔ ∃ z, hE.connecting d j z = x :=
  NativeFiber.exact_fiber _ (hE.fiberTriangle_isFiber d) j x

lemma exact_middle (j : ℤ) (x : hE.group d 1 0 j) :
    hE.projection d j x = 1 ↔ ∃ z, hE.inclusion d j z = x :=
  NativeFiber.exact_total _ (hE.fiberTriangle_isFiber d) j x

lemma exact_right (j : ℤ) (x : hE.group d 1 1 (j + 1)) :
    hE.connecting d j x = 1 ↔ ∃ z, hE.projection d (j + 1) z = x :=
  NativeFiber.exact_base _ (hE.fiberTriangle_isFiber d) j x

end SerrePositivity.KST.LocalizingInvariants.IsRelativeLocalizingInvariant
