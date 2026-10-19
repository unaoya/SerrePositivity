module

public import SerrePositivity.KST.Spectra.NullHomotopyDifferenceComposition
public import SerrePositivity.KST.Spectra.NullHomotopyDifferenceIdentity

/-!
概要：零ホモトピーの選択変更に対する差の式。
方針：Kan 充填で証明した合成則と自己差の単位元から逆元と両端変更を導く。
規約：二段の差は π₂ 以上に属するので既存の可換群構造を用いる。
使われ方：Goerss–Jardine VIII §1。塔の lim¹ の twisted 作用。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.NullHomotopyDifference

noncomputable section

variable {X : SSet.{u}} [KanComplex X] {x : X _⦋0⦌} {n : ℕ}
  {s : X.PtSimplex (n + 1) x}

/-- 二つの零ホモトピーを交換すると差は逆元になる。 -/
theorem difference_inv (R S : PtSimplex.RelStruct .const s (Fin.last (n + 1))) :
    difference S R = (difference R S)⁻¹ := by
  calc
    difference S R = difference S R * (difference R S * (difference R S)⁻¹) := by simp
    _ = (difference S R * difference R S) * (difference R S)⁻¹ := by rw [mul_assoc]
    _ = (difference R S)⁻¹ := by rw [difference_comp, difference_self, one_mul]

/-- 差の両端を変更したときの三つの因子。 -/
theorem difference_change
    (R S R' S' : PtSimplex.RelStruct .const s (Fin.last (n + 1))) :
    difference R' S' = difference R' R * difference R S * (difference S' S)⁻¹ := by
  rw [← difference_inv S' S]
  calc
    difference R' S' = difference S S' * difference R' S := (difference_comp R' S S').symm
    _ = difference S S' * (difference R S * difference R' R) := by
      rw [difference_comp R' R S]
    _ = difference R' R * difference R S * difference S S' := by ac_rfl

end
end SerrePositivity.KST.Spectra.NullHomotopyDifference
