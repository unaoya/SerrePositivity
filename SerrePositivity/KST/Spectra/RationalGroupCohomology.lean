module

public import SerrePositivity.KST.Spectra.FiniteGroupAveraging
public import Mathlib.RepresentationTheory.FinGroupCharZero
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

/-!
概要：有限群の有理表現の正次数の群コホモロジーは零。
方針：位数の可逆性による平均化から得る射影性を使い、構成済みの bar resolution と Ext の比較で計算する。
規約：安定モデル構造や HT-KQ を使わない。次数零は消滅の主張に含めない。
使われ方：HA §1.4.2。L9e の Tot の有理比較の代数的入力。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity.KST.Spectra

/-- 概要：有限群の有理表現の正次数の群コホモロジーは零対象。
方針：平均化による射影性から Ext の正次数を零にし、bar cochain の比較同型で戻す。
規約：ℚ を含む標数零の体に一般化し、位数の非零性を明示的に供給する。
使われ方：BF 1978 §2。有理 homotopy fixed points の群の計算。 -/
theorem rationalGroupCohomology_isZero {k G : Type u} [Field k] [CharZero k]
    [Group G] [Finite G] (A : Rep k G) (n : ℕ) : IsZero (groupCohomology A (n + 1)) := by
  let : NeZero (Nat.card G : k) :=
    ⟨Nat.cast_ne_zero.mpr (Nat.card_pos (α := G)).ne'⟩
  exact (isZero_Ext_succ_of_projective (Rep.trivial k G k) A n).of_iso
    (groupCohomologyIsoExt A (n + 1))

end SerrePositivity.KST.Spectra
