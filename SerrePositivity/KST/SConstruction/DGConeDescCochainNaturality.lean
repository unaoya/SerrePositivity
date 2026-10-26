module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeRetraction

/-!
概要：実 cone からの指定比較の全次数自然性を、同じ二つの入力成分で証明する。
方針：元左右包含への制限で二成分を照合し、次数 −1 成分の符号を保持する。
規約：微分境界の証拠とは独立した全 Hom の等号。
使われ方：指定回転ホモトピーから作る cone 比較族の全自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R] {A B C D E E' : Complex R}
private lemma coneMapInl (f : A ⟶ B) (g : C ⟶ D) {n : ℤ}
    (a : Homogeneous A C n) (b : Homogeneous B D n) :
    (mappingCone.inl f).comp (coneMapCochain f g a b) (by omega : -1 + n = n - 1) =
      n.negOnePow • a.comp (mappingCone.inl g) (by omega : n + -1 = n - 1) := by
  apply Cochain.ext
  intro i j hij
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, i = k + 1 := ⟨i - 1, by omega⟩
  rw [Cochain.comp_v _ _ _ (k + 1) k j (by omega) (by omega),
    Cochain.units_smul_v, Cochain.comp_v _ _ _ (k + 1) (j + 1) j (by omega) (by omega)]
  exact coneMapCochain_inl_v _ _ _ _ k j (by omega)

/-- 概要：元 cone の指定二成分からの射は、同じ符号付き全自然性を保つ。
方針：元二包含で全 cochain を検出し、各入力の自然性と結合則を使う。
規約：全整数次数での等号を保持。使われ方：回転後の実 cone 比較の全 Hom 作用。 -/
lemma dgConeDescCochain_naturality (f : A ⟶ B) (g : C ⟶ D) {n : ℤ}
    (a : Homogeneous A C n) (b : Homogeneous B D n) (c : Homogeneous E E' n)
    (h : Homogeneous A E (-1)) (h' : Homogeneous C E' (-1))
    (q : Homogeneous B E 0) (q' : Homogeneous D E' 0)
    (hh : h.comp c (by omega : -1 + n = n - 1) =
      n.negOnePow • a.comp h' (by omega : n + -1 = n - 1))
    (hq : b.comp q' (add_zero n) = q.comp c (zero_add n)) :
    (coneMapCochain f g a b).comp (mappingCone.descCochain g h' q' (by omega))
        (add_zero n) =
      (mappingCone.descCochain f h q (by omega)).comp c (zero_add n) := by
  apply (mappingCone.ext_cochain_from_iff f (n - 1) n (by omega)).2
  constructor
  · calc
      _ = ((mappingCone.inl f).comp (coneMapCochain f g a b) (by omega)).comp
          (mappingCone.descCochain g h' q' (by omega)) (add_zero (n - 1)) :=
        (Cochain.comp_assoc_of_third_is_zero_cochain _ _ _ (by omega)).symm
      _ = (n.negOnePow • a.comp (mappingCone.inl g) (by omega)).comp
          (mappingCone.descCochain g h' q' (by omega)) (add_zero (n - 1)) :=
        congrArg (fun t => t.comp (mappingCone.descCochain g h' q' (by omega))
          (add_zero (n - 1))) (coneMapInl f g a b)
      _ = n.negOnePow • a.comp h' (by omega) := by
        rw [Cochain.units_smul_comp, Cochain.comp_assoc_of_third_is_zero_cochain,
          mappingCone.inl_descCochain]
      _ = h.comp c (by omega) := hh.symm
      _ = ((mappingCone.inl f).comp (mappingCone.descCochain f h q (by omega))
          (add_zero (-1))).comp c (by omega) := by rw [mappingCone.inl_descCochain]
      _ = _ := Cochain.comp_assoc_of_second_is_zero_cochain _ _ _ (by omega)
  · calc
      _ = ((Cochain.ofHom (mappingCone.inr f)).comp (coneMapCochain f g a b)
          (zero_add n)).comp (mappingCone.descCochain g h' q' (by omega)) (add_zero n) :=
        (Cochain.comp_assoc_of_first_is_zero_cochain _ _ _ (add_zero n)).symm
      _ = (b.comp (Cochain.ofHom (mappingCone.inr g)) (add_zero n)).comp
          (mappingCone.descCochain g h' q' (by omega)) (add_zero n) :=
        congrArg (fun t => t.comp (mappingCone.descCochain g h' q' (by omega))
          (add_zero n)) (coneMapCochain_inr f g a b)
      _ = b.comp q' (add_zero n) := by
        rw [Cochain.comp_assoc_of_third_is_zero_cochain, mappingCone.inr_descCochain]
      _ = q.comp c (zero_add n) := hq
      _ = ((Cochain.ofHom (mappingCone.inr f)).comp
          (mappingCone.descCochain f h q (by omega)) (zero_add 0)).comp c (zero_add n) := by
        rw [mappingCone.inr_descCochain]
      _ = _ := Cochain.comp_assoc_of_first_is_zero_cochain _ _ _ (zero_add n)
end SerrePositivity.KST.SConstruction
