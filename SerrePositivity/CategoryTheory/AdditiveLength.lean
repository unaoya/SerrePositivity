module

public import SerrePositivity.CategoryTheory.SerreLength

/-! # 非負加法的な長さと零長さの Serre 部分圏

長さの単調性と零長さの Serre 条件を、加群や列の実現と独立に証明する。
値域は順序付き可換加法モノイドで、実数と非負拡大実数の双方に使う。忠実性は仮定しない。
-/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

variable {L : Type*} [AddCommMonoid L] [PartialOrder L] [IsOrderedAddMonoid L]
  {C : Type*} [Category* C] [Abelian C] (l : C → L)
  (ha : ∀ {S : ShortComplex C}, S.ShortExact → l S.X₂ = l S.X₁ + l S.X₃)
  (hn : ∀ X, 0 ≤ l X)

include ha hn in
/-- 単射に沿う長さの単調性。 -/
lemma additiveLength_le_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] : l X ≤ l Y := by
  have h := ha (show (ShortComplex.mk f (cokernel.π f)
    (cokernel.condition f)).ShortExact from { exact := ShortComplex.exact_cokernel f })
  change l Y = l X + l (cokernel f) at h
  rw [h]
  exact le_add_of_nonneg_right (hn _)

include ha hn in
/-- 全射に沿う長さの単調性。 -/
lemma additiveLength_le_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] : l Y ≤ l X := by
  have h := ha (show (ShortComplex.mk (kernel.ι f) f
    (kernel.condition f)).ShortExact from { exact := ShortComplex.exact_kernel f })
  change l X = l (kernel f) + l Y at h
  rw [h]
  exact le_add_of_nonneg_left (hn _)

include ha hn in
/-- 直和因子の長さは元の対象の長さ以下。 -/
lemma additiveLength_le_of_retract {X Y : C} (r : Retract X Y) : l X ≤ l Y :=
  additiveLength_le_of_mono l ha hn r.i

/-- 零長さの対象。 -/
def zeroAdditiveLength : ObjectProperty C := fun X ↦ l X = 0

include ha hn in
/-- 非負で短完全列に加法的な長さの零対象は Serre 部分圏をなす。 -/
lemma zeroAdditiveLength_isSerreClass (hz : l 0 = 0) :
    (zeroAdditiveLength l).IsSerreClass where
  exists_zero := ⟨0, isZero_zero _, hz⟩
  prop_of_mono f _ hY := le_antisymm
    ((additiveLength_le_of_mono l ha hn f).trans_eq hY) (hn _)
  prop_of_epi f _ hX := le_antisymm
    ((additiveLength_le_of_epi l ha hn f).trans_eq hX) (hn _)
  prop_X₂_of_shortExact hS h₁ h₃ := by
    change l _ = 0
    rw [ha hS, h₁, h₃, add_zero]

end SerrePositivity
