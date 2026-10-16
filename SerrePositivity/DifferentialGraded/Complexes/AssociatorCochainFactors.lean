module
public import SerrePositivity.DifferentialGraded.Complexes.AssociatorCochainNaturality
public import SerrePositivity.DifferentialGraded.Complexes.TensorRightComposition

/-! # associatorの左・中間因子の全次数cochain自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 左括弧の三重tensor上の任意次数cochainは純tensorで判定できる。 -/
lemma leftTripleCochain_ext {P Q R T : Complex A} {p : ℤ}
    (f g : Cochain ((P ⊗ Q) ⊗ R) T p)
    (h : ∀ (i j k a n : ℤ) (ha : i + j + k = a) (hn : a + p = n)
      (x : P.X i) (y : Q.X j) (z : R.X k),
      f.v a n hn (ιTensorObj (P ⊗ Q) R (i + j) k a ha
        (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z)) =
      g.v a n hn (ιTensorObj (P ⊗ Q) R (i + j) k a ha
        (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z))) : f = g := by
  apply Cochain.ext
  intro a n hn
  apply SerrePositivity.cochainTensorTriple_hom_ext P Q R a
  intro i j k ha
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  exact h i j k a n ha hn x y z

lemma associator_hom_cochain_left (P P' Q R : Complex A) (p : ℤ) (f : Cochain P P' p) :
    ((tensorRightHom R (P ⊗ Q) (P' ⊗ Q)).f p
      ((tensorRightHom Q P P').f p f)).comp (Cochain.ofHom (α_ P' Q R).hom) (add_zero p) =
    (Cochain.ofHom (α_ P Q R).hom).comp
      ((tensorRightHom (Q ⊗ R) P P').f p f) (zero_add p) := by
  apply leftTripleCochain_ext
  intro i j k a n ha hn x y z
  rw [cochain_comp_ofHom_apply, cochain_ofHom_comp_apply, tensorRightHom_apply,
    tensorRightHom_apply_of_sum Q P P' p i j (i + j) (i + p) (i + j + p) rfl rfl rfl,
    associator_apply_of_sum P' Q R (i + p) j k (i + j + p) n (by omega) (by omega),
    associator_apply, tensorRightHom_apply]

lemma associator_hom_cochain_middle (K P P' R : Complex A) (p : ℤ) (f : Cochain P P' p) :
    ((tensorRightHom R (K ⊗ P) (K ⊗ P')).f p
      ((tensorLeftHom K P P').f p f)).comp (Cochain.ofHom (α_ K P' R).hom) (add_zero p) =
    (Cochain.ofHom (α_ K P R).hom).comp
      ((tensorLeftHom K (P ⊗ R) (P' ⊗ R)).f p
        ((tensorRightHom R P P').f p f)) (zero_add p) := by
  apply leftTripleCochain_ext
  intro i j k a n ha hn x y z
  rw [cochain_comp_ofHom_apply, cochain_ofHom_comp_apply, tensorRightHom_apply,
    tensorLeftHom_apply_of_sum K P P' p i j (i + j) (j + p) (i + j + p) rfl rfl rfl,
    associator_apply]
  simp only [Units.smul_def, TensorProduct.smul_tmul]
  rw [associator_apply_of_sum K P' R i (j + p) k (i + j + p) n (by omega) (by omega),
    tensorLeftHom_apply_of_sum K (P ⊗ R) (P' ⊗ R) p i (j + k) a (j + p + k) n
      (by omega) (by omega) hn,
    tensorRightHom_apply]
  simp only [Units.smul_def, TensorProduct.tmul_smul, map_zsmul]

end SerrePositivity.DifferentialGraded
