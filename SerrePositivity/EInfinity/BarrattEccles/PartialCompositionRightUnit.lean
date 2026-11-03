module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleRightUnit
public import SerrePositivity.EInfinity.BarrattEccles.Unitors
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

/-!
# 部分合成の複体の射の右単位則

概要：Berger–Fresse §1.1.3 の右単位則を既存のコチェインテンソルの右単位子と比較する。
方針：右単位子の逆を前合成し、単位と元の純粋テンソルの部分合成を計算する。
規約：外側 arity は m+1、挿入位置 i は任意である。
使われ方：Barratt–Eccles オペラッドの comp_unit を与える。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：部分合成へ右から単位を代入する射は右単位子である（Berger–Fresse §1.1.3）。
方針：右単位子の逆を前合成し、負の次数では単位の純粋テンソル、正次数では零元で比較する。
規約：既存のテンソルの右単位子を用い、新たなモノイダル構造は作らない。
使われ方：Barratt–Eccles オペラッドの右単位則となる。 -/
lemma partialComposition_right_unit (m : ℕ) (i : Fin (m + 1)) :
    (complex A (m + 1) ◁ unit A) ≫ partialComposition A m 1 i =
      (ρ_ (complex A (m + 1))).hom := by
  apply (cancel_epi (ρ_ (complex A (m + 1))).inv).1
  rw [Iso.inv_hom_id]
  apply HomologicalComplex.hom_ext
  intro r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (partialComposition A m 1 i).f r
    ((complex A (m + 1) ◁ unit A).f r ((ρ_ (complex A (m + 1))).inv.f r x)) = x
  by_cases hr : 0 < r
  · have hx := complex_eq_zero_of_positive A (m + 1) r hr x
    simp only [hx, map_zero]
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, r = -(p : ℤ) := ⟨(-r).toNat, by omega⟩
  rw [cochain_rightUnitor_inv_apply A,
    SerrePositivity.DifferentialGraded.whiskerLeft_apply (complex A (m + 1)) (unit A)
      (-(p : ℤ)) 0 (-(p : ℤ)) (add_zero _) x
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)),
    partialComposition_right_unit_tmul A m i p x 1, one_smul]

end SerrePositivity.EInfinity.BarrattEccles
