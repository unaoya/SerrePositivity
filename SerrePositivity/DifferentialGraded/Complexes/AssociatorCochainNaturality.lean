module
public import SerrePositivity.DifferentialGraded.Complexes.TensorClosedZero
public import SerrePositivity.DifferentialGraded.Complexes.TensorRightHom

/-! # associatorの第三因子に関する全次数自然性

閉零chain mapに限らず、任意整数次数のcochainについてtensorの括弧変更と可換する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- associatorは第三因子の任意次数cochainと可換する。 -/
lemma associator_hom_cochain_right (P Q R S : Complex A) (p : ℤ) (f : Cochain R S p) :
    ((tensorLeftHom (P ⊗ Q) R S).f p f).comp
      (Cochain.ofHom (α_ P Q S).hom) (add_zero p) =
    (Cochain.ofHom (α_ P Q R).hom).comp
      ((tensorLeftHom P (Q ⊗ R) (Q ⊗ S)).f p
        ((tensorLeftHom Q R S).f p f)) (zero_add p) := by
  apply Cochain.ext
  intro a n hn
  apply SerrePositivity.cochainTensorTriple_hom_ext P Q R a
  intro i j k ha
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  change
    (((tensorLeftHom (P ⊗ Q) R S).f p f).comp
      (Cochain.ofHom (α_ P Q S).hom) (add_zero p)).v a n hn
      (ιTensorObj (P ⊗ Q) R (i + j) k a ha
        (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z)) =
    ((Cochain.ofHom (α_ P Q R).hom).comp
      ((tensorLeftHom P (Q ⊗ R) (Q ⊗ S)).f p
        ((tensorLeftHom Q R S).f p f)) (zero_add p)).v a n hn
      (ιTensorObj (P ⊗ Q) R (i + j) k a ha
        (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z))
  rw [cochain_comp_ofHom_apply, cochain_ofHom_comp_apply,
    tensorLeftHom_apply_of_sum (P ⊗ Q) R S p (i + j) k a (k + p) n ha rfl hn,
    chain_units_smul, associator_apply, associator_apply,
    tensorLeftHom_apply_of_sum P (Q ⊗ R) (Q ⊗ S) p i (j + k) a (j + (k + p)) n
      (by omega) (by omega) hn,
    tensorLeftHom_apply_of_sum Q R S p j k (j + k) (k + p) (j + (k + p))
      rfl rfl (by omega)]
  simp only [Units.smul_def, TensorProduct.tmul_smul, map_zsmul, smul_smul]
  congr 2
  rw [mul_add, Int.negOnePow_add]
  rfl

/-- 逆associatorも第三因子の任意次数cochainと可換する。 -/
lemma associator_inv_cochain_right (P Q R S : Complex A) (p : ℤ) (f : Cochain R S p) :
    ((tensorLeftHom P (Q ⊗ R) (Q ⊗ S)).f p
      ((tensorLeftHom Q R S).f p f)).comp
      (Cochain.ofHom (α_ P Q S).inv) (add_zero p) =
    (Cochain.ofHom (α_ P Q R).inv).comp
      ((tensorLeftHom (P ⊗ Q) R S).f p f) (zero_add p) := by
  apply Cochain.ext
  intro i n hn
  apply (cancel_epi ((α_ P Q R).hom.f i)).1
  have h := congrArg (fun z : Cochain ((P ⊗ Q) ⊗ R) (P ⊗ (Q ⊗ S)) p => z.v i n hn)
    (associator_hom_cochain_right P Q R S p f)
  simp only [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v] at h ⊢
  have hR : (α_ P Q R).hom.f i ≫ (α_ P Q R).inv.f i = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]
  have hS : (α_ P Q S).hom.f n ≫ (α_ P Q S).inv.f n = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]
  rw [← Category.assoc, ← h, Category.assoc, hS, Category.comp_id,
    ← Category.assoc, hR, Category.id_comp]

/-- 左因子のchain mapに対するtensorの自然性を、任意次数のcochainに取り出す。 -/
lemma tensorLeftHom_cochain_naturality {K L : Complex A} (c : K ⟶ L)
    (P Q : Complex A) (p : ℤ) (f : Cochain P Q p) :
    ((tensorLeftHom K P Q).f p f).comp (Cochain.ofHom (c ▷ Q)) (add_zero p) =
    (Cochain.ofHom (c ▷ P)).comp ((tensorLeftHom L P Q).f p f) (zero_add p) := by
  have h := congrArg (fun t : homComplex A P Q ⟶ homComplex A (K ⊗ P) (L ⊗ Q) => t.f p f)
    (tensorLeftHom_naturality c P Q)
  change (((tensorLeftHom K P Q).f p f).comp
    (Cochain.ofHom (c ⊗ₘ 𝟙 Q)) (add_zero p)) =
    (Cochain.ofHom (c ⊗ₘ 𝟙 P)).comp ((tensorLeftHom L P Q).f p f) (zero_add p) at h
  simpa only [tensorHom_id] using h

/-- 前方の二因子の合成と括弧変更は、残る右因子の任意次数cochainと可換する。 -/
lemma tensorJoin_cochain_naturality (U V W P Q : Complex A) (c : U ⊗ V ⟶ W)
    (p : ℤ) (f : Cochain P Q p) :
    (Cochain.ofHom ((α_ U V P).inv ≫ (c ▷ P))).comp
      ((tensorLeftHom W P Q).f p f) (zero_add p) =
    ((tensorLeftHom U (V ⊗ P) (V ⊗ Q)).f p
      ((tensorLeftHom V P Q).f p f)).comp
      (Cochain.ofHom ((α_ U V Q).inv ≫ (c ▷ Q))) (add_zero p) := by
  rw [Cochain.ofHom_comp, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain,
    ← tensorLeftHom_cochain_naturality,
    ← Cochain.comp_assoc_of_third_is_zero_cochain,
    ← associator_inv_cochain_right, Cochain.comp_assoc_of_third_is_zero_cochain]

end SerrePositivity.DifferentialGraded
