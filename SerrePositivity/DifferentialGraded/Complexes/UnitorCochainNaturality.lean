module
public import SerrePositivity.DifferentialGraded.Complexes.TensorRightHom
public import SerrePositivity.DifferentialGraded.Complexes.TensorClosedZero

/-! # 左unitorと全整数次数cochainの整合性

閉零射の自然性を任意次数のcochainへ拡張する。逆unitorを純tensorで評価して証明する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 逆左unitorは単位の標準生成元を左に置く。 -/
lemma complexLeftUnitor_inv_apply (P : Complex A) (i : ℤ) (x : P.X i) :
    (λ_ P).inv.f i x = ιTensorObj (𝟙_ (Complex A)) P 0 i i (zero_add i)
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] x) := by
  change (leftUnitor' P).inv i x = _
  rw [leftUnitor'_inv]
  rfl

/-- 左unitorは標準単位生成元を除く。 -/
lemma leftUnitor_hom_generator (P : Complex A) (i : ℤ) (x : P.X i) :
    (λ_ P).hom.f i (ιTensorObj (𝟙_ (Complex A)) P 0 i i (zero_add i)
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] x)) = x := by
  rw [← complexLeftUnitor_inv_apply]
  change ((λ_ P).inv ≫ (λ_ P).hom).f i x = x
  rw [Iso.inv_hom_id]
  rfl

/-- 逆左unitorは全次数cochainに関して自然。 -/
lemma leftUnitor_inv_cochain (P Q : Complex A) (p : ℤ) (f : Cochain P Q p) :
    (Cochain.ofHom (λ_ P).inv).comp ((tensorLeftHom (𝟙_ (Complex A)) P Q).f p f)
      (zero_add p) = f.comp (Cochain.ofHom (λ_ Q).inv) (add_zero p) := by
  apply Cochain.ext
  intro i n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [cochain_ofHom_comp_apply, cochain_comp_ofHom_apply, complexLeftUnitor_inv_apply,
    tensorLeftHom_apply_of_sum (𝟙_ (Complex A)) P Q p 0 i i n n (zero_add i) hn hn,
    complexLeftUnitor_inv_apply]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]

/-- 左unitorは全次数cochainに関して自然。 -/
lemma leftUnitor_hom_cochain (P Q : Complex A) (p : ℤ) (f : Cochain P Q p) :
    ((tensorLeftHom (𝟙_ (Complex A)) P Q).f p f).comp (Cochain.ofHom (λ_ Q).hom)
      (add_zero p) = (Cochain.ofHom (λ_ P).hom).comp f (zero_add p) := by
  apply Cochain.ext
  intro i n hn
  apply (cancel_epi ((λ_ P).inv.f i)).1
  have h := congrArg (fun z : Cochain P (𝟙_ (Complex A) ⊗ Q) p => z.v i n hn)
    (leftUnitor_inv_cochain P Q p f)
  simp only [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v] at h ⊢
  have hP : (λ_ P).inv.f i ≫ (λ_ P).hom.f i = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  have hQ : (λ_ Q).inv.f n ≫ (λ_ Q).hom.f n = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  rw [← Category.assoc, h, Category.assoc, hQ, Category.comp_id,
    ← Category.assoc, hP, Category.id_comp]

/-- 任意の前方因子を置いた左unitorも全次数cochainと可換する。 -/
lemma leftUnitor_hom_cochain_tensor (K P Q : Complex A) (p : ℤ) (f : Cochain P Q p) :
    ((tensorLeftHom K (𝟙_ (Complex A) ⊗ P) (𝟙_ (Complex A) ⊗ Q)).f p
      ((tensorLeftHom (𝟙_ (Complex A)) P Q).f p f)).comp
      (Cochain.ofHom (K ◁ (λ_ Q).hom)) (add_zero p) =
    (Cochain.ofHom (K ◁ (λ_ P).hom)).comp
      ((tensorLeftHom K P Q).f p f) (zero_add p) := by
  rw [← tensorLeftHom_ofHom K _ _ (λ_ Q).hom,
    ← tensorLeftHom_ofHom K _ _ (λ_ P).hom,
    ← tensorLeftHom_cochain_comp, ← tensorLeftHom_cochain_comp, leftUnitor_hom_cochain]

end SerrePositivity.DifferentialGraded
