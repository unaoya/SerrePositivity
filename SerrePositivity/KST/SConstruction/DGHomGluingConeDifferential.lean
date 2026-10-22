module
public import SerrePositivity.KST.SConstruction.DGHomGluingConeCochain

/-! # 第三比較を持つ cone 作用の捻れた微分
概要：比較差と第三成分の微分を保持し、同じ実 cone cochain の微分を計算する。
方針：元の liftCochain の微分と fst・snd の二式を適用する。
規約：可換 square の仮定を置かない。使われ方：全 gluing Hom の鎖写像性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
variable {R : Type u} [CommRing R] {A B C D : Complex R}

/-- 同じ三成分作用の微分は、元の比較差を第三成分に持つ同じ作用。 -/
lemma dgGluingConeCochain_differential (f : A ⟶ B) (g : C ⟶ D) {n m : ℤ}
    (a : Homogeneous A C n) (b : Homogeneous B D n) (h : Homogeneous A D m) (hm : m + 1 = n) :
    δ n (n + 1) (dgGluingConeCochain f g a b h hm) =
      dgGluingConeCochain f g (δ n (n + 1) a) (δ n (n + 1) b)
        (a.comp (Cochain.ofHom g) (add_zero n) -
          (Cochain.ofHom f).comp b (zero_add n) - δ m n h) rfl := by
  unfold dgGluingConeCochain
  rw [mappingCone.δ_liftCochain g _ _ rfl (n + 1 + 1) rfl]
  simp only [δ_sub, δ_units_smul]
  rw [δ_comp (mappingCone.fst f).val a (by omega : 1 + n = n + 1)
    2 (n + 1) (n + 1 + 1) rfl rfl rfl]
  rw [δ_comp (mappingCone.snd f) b (zero_add n) 1 (n + 1) (n + 1) rfl (zero_add 1) rfl]
  rw [δ_comp (mappingCone.fst f).val h (by omega : 1 + m = n)
    2 n (n + 1) rfl rfl hm]
  simp only [Cocycle.δ_eq_zero, Cochain.zero_comp, smul_zero, add_zero, mappingCone.δ_snd]
  simp only [Cochain.units_smul_comp, Cochain.neg_comp, Cochain.comp_sub]
  simp only [Cochain.comp_assoc_of_second_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain]
  simp only [mappingCone.liftCochain, Int.negOnePow_succ, Units.neg_smul,
    Cochain.neg_comp, Cochain.sub_comp,
    Cochain.units_smul_comp]
  simp only [Cochain.add_comp, Cochain.sub_comp, Cochain.neg_comp,
    Cochain.units_smul_comp, smul_sub, smul_neg]
  abel

end SerrePositivity.KST.SConstruction
