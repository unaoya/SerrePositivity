module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SignedShiftBlockValues
public import SerrePositivity.HomologicalAlgebra.UnsignedShiftCochain
import all SerrePositivity.HomologicalAlgebra.UnsignedShiftCochain

/-!
# 同じ一次 shift ブロックの後の列の合成

## 概要
符号を相殺したブロックにシフトされた列を合成し、元の係数の後の同じ列に戻す。

## 方針
二つの次数同型を同じ中間次数で評価し、その逆と順写像を打ち消す。

## 規約
列は閉じていると仮定せず、元の cochain の全成分を保つ。

## 使われ方
HA 1.2.4。theta の一次列の後合成と単体境界の項の同定。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
variable (A : Type u) [CommRing A]

private theorem unsignedShift_at {K L : Complex A} {r : ℤ} (z : Cochain K L r)
    (a r' : ℤ) (h : r + a = r') (p q : ℤ) (hpq : p + r' = q) (p' : ℤ) (hp' : p' + r = q) :
    (unsignedLeftShift z a r' h).v p q hpq =
      (K.shiftFunctorObjXIso a p p' (by omega)).hom ≫ z.v p' q hp' := by
  simp only [unsignedLeftShift, Cochain.units_smul_v, z.leftShift_v a r' h p q hpq p' hp',
    smul_smul, Int.units_mul_self, one_smul]

/-- 符号つき一次ブロックの後の列は、元の係数と同じ列の合成のシフトそのもの。 -/
theorem signedShiftBlock_comp (n : ℕ) (M N : RightModule A PUnit.{1}) (T : Complex A)
    (f : (moduleHom A PUnit.{1} M N).X 0) (z : Cochain (N.obj (op PUnit.unit)) T (-(n : ℤ))) :
    ((moduleHomπ A PUnit.{1} (shiftModule ((n + 1 : ℕ) : ℤ) M) (shiftModule (n : ℤ) N)
      PUnit.unit).f 1 (((n + 1 : ℕ) : ℤ).negOnePow •
        moduleHomShiftBlock A PUnit.{1} ((n + 1 : ℕ) : ℤ) (n : ℤ) f (by omega))).comp
      (unsignedLeftShift z (n : ℤ) 0 (by omega)) (add_zero 1) =
    unsignedLeftShift
      (((moduleHomπ A PUnit.{1} M N PUnit.unit).f 0 f).comp z (zero_add _))
      ((n + 1 : ℕ) : ℤ) 1 (by omega) := by
  apply Cochain.ext
  intro p q hpq
  have hq : q = p + 1 := by omega
  cases hq
  rw [Cochain.comp_v _ _ (add_zero 1) p (p + 1) (p + 1) rfl (by omega), signedShiftBlock_v]
  rw [unsignedShift_at A z (n : ℤ) 0 (by omega) (p + 1) (p + 1) (by omega)
      (p + ((n + 1 : ℕ) : ℤ)) (by omega)]
  rw [unsignedShift_at A _ ((n + 1 : ℕ) : ℤ) 1 (by omega) p (p + 1) rfl
      (p + ((n + 1 : ℕ) : ℤ)) (by omega)]
  rw [Cochain.comp_v _ _ (zero_add _) (p + ((n + 1 : ℕ) : ℤ))
      (p + ((n + 1 : ℕ) : ℤ)) (p + 1) (by omega) (by omega)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
