module
public import SerrePositivity.KST.SConstruction.DGHomGluingConeDifferential

/-! # 第三比較を保持する cone 作用の合成
概要：比較ホモトピー成分を落とさず、同じ cone cochain の斉次合成を計算する。
方針：元の二射影で等号を判定し、shift の符号を元の次数和にまとめる。
規約：可換 square の仮定を置かない。使われ方：全 gluing Hom の合成保存。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
variable {R : Type u} [CommRing R] {A B C D E F : Complex R}

/-- 第三比較の合成は左成分との合成と、右次数の符号を持つ右成分との合成。 -/
lemma dgGluingConeCochain_comp
    (f : A ⟶ B) (g : C ⟶ D) (j : E ⟶ F) {n m p l : ℤ}
    (a : Homogeneous A C n) (b : Homogeneous B D n) (h : Homogeneous A D m)
    (hm : m + 1 = n) (c : Homogeneous C E p) (d : Homogeneous D F p)
    (k : Homogeneous C F l) (hl : l + 1 = p) :
    (dgGluingConeCochain f g a b h hm).comp
        (dgGluingConeCochain g j c d k hl) rfl =
      dgGluingConeCochain f j (a.comp c rfl) (b.comp d rfl)
        (a.comp k (by omega : n + l = m + p) + p.negOnePow • h.comp d rfl)
        (by omega) := by
  apply (mappingCone.ext_cochain_to_iff j (n + p) (n + p + 1) rfl).2
  constructor
  · rw [Cochain.comp_assoc _ _ _ rfl rfl (by omega), dgGluingConeCochain_fst,
      Cochain.comp_units_smul]
    rw [← Cochain.comp_assoc _ _ _ rfl (by omega : 1 + p = p + 1) (by omega),
      dgGluingConeCochain_fst, Cochain.units_smul_comp,
      Cochain.comp_assoc _ _ _ (by omega : 1 + n = n + 1) rfl (by omega),
      dgGluingConeCochain_fst, smul_smul, ← Int.negOnePow_add, add_comm p n]
  · rw [Cochain.comp_assoc_of_third_is_zero_cochain, dgGluingConeCochain_snd]
    simp only [Cochain.comp_sub, Cochain.comp_units_smul]
    rw [← Cochain.comp_assoc_of_second_is_zero_cochain, dgGluingConeCochain_snd]
    rw [← Cochain.comp_assoc _ _ _ rfl (by omega : 1 + l = p) (by omega),
      dgGluingConeCochain_fst]
    rw [dgGluingConeCochain_snd]
    simp only [Cochain.sub_comp, Cochain.units_smul_comp, Cochain.comp_add,
      Cochain.comp_units_smul, smul_add, smul_smul, ← Int.negOnePow_add]
    simp only [add_comm p n, Int.negOnePow_add]
    rw [mul_assoc, Int.units_mul_self, mul_one]
    erw [Cochain.comp_assoc _ _ _ (zero_add n) rfl (by omega),
      Cochain.comp_assoc _ _ _ (by omega : 1 + m = n) rfl (by omega),
      Cochain.comp_assoc _ _ _ (by omega : 1 + n = n + 1)
        (by omega : n + l = m + p) (by omega)]
    abel

end SerrePositivity.KST.SConstruction
