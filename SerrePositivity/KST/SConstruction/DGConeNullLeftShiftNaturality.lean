module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeNullHomotopy
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction

/-!
概要：指定次数 −1 零化元の始域 shift は次数零の全自然性を持つ。
方針：同じ成分の始域 shift と元 Hom shift の Koszul 符号を照合する。
規約：元指定零化元を保持。使われ方：回転比較の同じ左包含成分の全自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex DifferentialGraded

/-- 概要：次数 −1 の符号付き全自然性は始域 shift 後の次数零自然性を与える。
方針：同じ cochain の成分と shift の符号を直接照合する。
規約：元整数次数を保持。使われ方：実回転比較の左包含成分。 -/
lemma dgConeNullLeftShift_naturality {R : Type u} [CommRing R]
    {A B C D : Complex R} {n : ℤ}
    (a : Homogeneous A B n) (b : Homogeneous C D n)
    (z : Homogeneous A C (-1)) (z' : Homogeneous B D (-1))
    (h : z.comp b (neg_add_eq_sub 1 n) =
      n.negOnePow • a.comp z' (sub_eq_add_neg n 1).symm) :
    (z.leftShift 1 0 (neg_add_cancel 1)).comp b (zero_add n) =
      ((shiftHom 1 A B).f n a).comp (z'.leftShift 1 0 (neg_add_cancel 1)) (add_zero n) := by
  apply Cochain.ext
  intro i j hij
  rw [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v,
    Cochain.leftShift_v _ 1 0 (neg_add_cancel 1) i i (add_zero i) (i + 1) (by omega),
    Cochain.leftShift_v _ 1 0 (neg_add_cancel 1) j j (add_zero j) (j + 1) (by omega),
    shiftHom_v]
  simp only [zero_mul, mul_zero, one_mul, sub_self, mul_zero, Int.zero_ediv,
    add_zero, Int.negOnePow_zero, one_smul, CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp,
    Linear.units_smul_comp]
  have he := Cochain.congr_v h (i + 1) j (by omega)
  rw [Cochain.comp_v _ _ _ (i + 1) i j (by omega) hij,
    Cochain.units_smul_v, Cochain.comp_v _ _ _ (i + 1) (j + 1) j (by omega) (by omega)] at he
  exact he
end SerrePositivity.KST.SConstruction
