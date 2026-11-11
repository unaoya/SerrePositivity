module
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoin

/-!
概要：全次数 cochain の tensor と、単位を挿入する実鎖写像との自然性。
方針：全 cochain の交差符号と、左右単位子の実成分を使う。
規約：任意の整数次数。使われ方：出力分解 Hom の単位律の比較 cochain。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {R : Type u} [CommRing R]
/-- 右単位子の逆も、全次数 cochain と可換。 -/
lemma complexRightUnitor_inv_cochain (P Q : Complex R) (p : ℤ) (f : Cochain P Q p) :
    (Cochain.ofHom (ρ_ P).inv).comp ((tensorRightHom (𝟙_ (Complex R)) P Q).f p f)
      (zero_add p) = f.comp (Cochain.ofHom (ρ_ Q).inv) (add_zero p) := by
  apply Cochain.ext
  intro i n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [cochain_ofHom_comp_apply, cochain_comp_ofHom_apply, complexRightUnitor_inv_apply,
    tensorRightHom_apply_of_sum (𝟙_ (Complex R)) P Q p i 0 i n n (add_zero i) hn hn,
    complexRightUnitor_inv_apply]
/-- 左 tensor 因子上の実鎖写像は、右因子上の全 cochain と可換。 -/
lemma complexLeftTensor_cochain_chain_naturality (K L P Q : Complex R) (p : ℤ)
    (f : K ⟶ L) (h : Cochain P Q p) :
    (Cochain.ofHom (f ▷ P)).comp ((tensorLeftHom L P Q).f p h) (zero_add p) =
      ((tensorLeftHom K P Q).f p h).comp (Cochain.ofHom (f ▷ Q)) (add_zero p) := by
  have he := tensorCochain_interchange K L P Q 0 p p (zero_add p) (add_zero p)
    (Cochain.ofHom f) h
  simpa only [zero_mul, Int.negOnePow_zero, one_smul, tensorRightHom_ofHom] using he
/-- 左への実単位挿入は、右側の全 cochain と可換。 -/
lemma complexLeftUnitInsertion_cochain {K P Q : Complex R} (i : 𝟙_ (Complex R) ⟶ K)
    (p : ℤ) (h : Cochain P Q p) :
    (Cochain.ofHom ((λ_ P).inv ≫ i ▷ P)).comp
      ((tensorLeftHom K P Q).f p h) (zero_add p) =
    h.comp (Cochain.ofHom ((λ_ Q).inv ≫ i ▷ Q)) (add_zero p) := by
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    complexLeftTensor_cochain_chain_naturality,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, leftUnitor_inv_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp]
/-- 右への実単位挿入は、左側の全 cochain と可換。 -/
lemma complexRightUnitInsertion_cochain {K P Q : Complex R} (i : 𝟙_ (Complex R) ⟶ K)
    (p : ℤ) (h : Cochain P Q p) :
    (Cochain.ofHom ((ρ_ P).inv ≫ P ◁ i)).comp
      ((tensorRightHom K P Q).f p h) (zero_add p) =
    h.comp (Cochain.ofHom ((ρ_ Q).inv ≫ Q ◁ i)) (add_zero p) := by
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    tensorRight_cochain_chain_naturality,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, complexRightUnitor_inv_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp]
/-- 左の実単位で零となる cochain は、その右 tensor と左単位挿入でも零。 -/
lemma complexLeftUnitInsertion_rightTensor_zero {K L P : Complex R}
    (i : 𝟙_ (Complex R) ⟶ K) (p : ℤ) (h : Cochain K L p)
    (hi : (Cochain.ofHom i).comp h (zero_add p) = 0) :
    (Cochain.ofHom ((λ_ P).inv ≫ i ▷ P)).comp
      ((tensorRightHom P K L).f p h) (zero_add p) = 0 := by
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    ← tensorRightHom_ofHom, ← tensorRightHom_cochain_comp, hi, map_zero, Cochain.comp_zero]
/-- 右の実単位で零となる cochain に対する対称な零化。 -/
lemma complexRightUnitInsertion_leftTensor_zero {K L P : Complex R}
    (i : 𝟙_ (Complex R) ⟶ K) (p : ℤ) (h : Cochain K L p)
    (hi : (Cochain.ofHom i).comp h (zero_add p) = 0) :
    (Cochain.ofHom ((ρ_ P).inv ≫ P ◁ i)).comp
      ((tensorLeftHom P K L).f p h) (zero_add p) = 0 := by
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    ← tensorLeftHom_ofHom, ← tensorLeftHom_cochain_comp, hi, map_zero, Cochain.comp_zero]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
