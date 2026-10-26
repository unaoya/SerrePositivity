module
public import SerrePositivity.KST.SConstruction.DGConeNullLeftShiftNaturality

/-!
概要：元閉比較の始域 shift を次数一の符号付き全自然性として保持する。
方針：元次数零の全自然性と始域・全 Hom shift の同じ符号を照合する。
規約：元の閉比較を保持。使われ方：実回転比較の第一成分の全関手族化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex DifferentialGraded

/-- 概要：次数零比較の全自然性は始域 shift 後の次数一の全自然性を与える。
方針：元 cochain と Hom shift の成分・符号を計算する。
規約：全整数次数を保持。使われ方：元回転比較の第一成分。 -/
lemma dgClosedLeftShift_naturality {R : Type u} [CommRing R]
    {A B C D : Complex R} {n : ℤ}
    (a : Homogeneous A B n) (b : Homogeneous C D n)
    (z : Homogeneous A C 0) (z' : Homogeneous B D 0)
    (h : z.comp b (zero_add n) = a.comp z' (add_zero n)) :
    (z.leftShift 1 1 (zero_add 1)).comp b (add_comm 1 n) =
      n.negOnePow • ((shiftHom 1 A B).f n a).comp
        (z'.leftShift 1 1 (zero_add 1)) rfl := by
  apply Cochain.ext
  intro i j hij
  rw [Cochain.comp_v _ _ _ i (i + 1) j rfl (by omega),
    Cochain.units_smul_v, Cochain.comp_v _ _ _ i (j - 1) j (by omega) (by omega),
    Cochain.leftShift_v _ 1 1 (zero_add 1) i (i + 1) rfl (i + 1) (add_zero _),
    Cochain.leftShift_v _ 1 1 (zero_add 1) (j - 1) j (by omega) j (add_zero _),
    shiftHom_v]
  simp only [one_mul, sub_self, mul_zero, Int.zero_ediv, add_zero,
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Category.id_comp, Linear.units_smul_comp, Linear.comp_units_smul,
    smul_smul, Int.units_mul_self, one_smul]
  have hs : n.negOnePow * ((1 : ℤ).negOnePow * n.negOnePow) = (1 : ℤ).negOnePow := by
    rw [mul_left_comm, Int.units_mul_self, mul_one]
  erw [Category.id_comp, ← Category.assoc, Cochain.v_comp_XIsoOfEq_hom]
  rw [hs]
  have he := Cochain.congr_v h (i + 1) j (by omega)
  rw [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v] at he
  exact congrArg (fun t => (1 : ℤ).negOnePow • t) he
end SerrePositivity.KST.SConstruction
