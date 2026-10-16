module
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochain
public import SerrePositivity.DifferentialGraded.Complexes.AssociatorCochainFactors
public import SerrePositivity.DifferentialGraded.Complexes.TensorCochainInterchange

/-! # 閉性を仮定しない次数0 tensorの合成・括弧変更 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma tensorZeroCochain_comp {P P' P'' Q Q' Q'' : Complex A}
    (f : Cochain P P' 0) (g : Cochain Q Q' 0)
    (f' : Cochain P' P'' 0) (g' : Cochain Q' Q'' 0) :
    (tensorZeroCochain f g).comp (tensorZeroCochain f' g') (zero_add 0) =
      tensorZeroCochain (f.comp f' (zero_add 0)) (g.comp g' (zero_add 0)) := by
  have h := tensorCochain_interchange P' P'' Q Q' 0 0 0 (zero_add 0) (zero_add 0) f' g
  simp only [mul_zero, Int.negOnePow_zero, one_smul] at h
  have hh := congrArg (fun t : Cochain (P' ⊗ Q) (P'' ⊗ Q') 0 =>
    ((tensorRightHom Q P P').f 0 f).comp
      (t.comp ((tensorLeftHom P'' Q' Q'').f 0 g') (zero_add 0)) (zero_add 0)) h.symm
  simpa only [tensorZeroCochain, tensorRightHom_cochain_comp, tensorLeftHom_cochain_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain] using hh

lemma tensorZeroCochain_assoc {P P' Q Q' R R' : Complex A}
    (f : Cochain P P' 0) (g : Cochain Q Q' 0) (h : Cochain R R' 0) :
    (tensorZeroCochain (tensorZeroCochain f g) h).comp
      (Cochain.ofHom (α_ P' Q' R').hom) (zero_add 0) =
    (Cochain.ofHom (α_ P Q R).hom).comp
      (tensorZeroCochain f (tensorZeroCochain g h)) (zero_add 0) := by
  apply Cochain.ext₀
  intro n
  apply SerrePositivity.cochainTensorTriple_hom_ext P Q R n
  intro i j k hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  change ((tensorZeroCochain (tensorZeroCochain f g) h).comp
      (Cochain.ofHom (α_ P' Q' R').hom) (zero_add 0)).v n n (add_zero n)
      (ιTensorObj (P ⊗ Q) R (i + j) k n hn
        (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z)) =
    ((Cochain.ofHom (α_ P Q R).hom).comp (tensorZeroCochain f (tensorZeroCochain g h))
      (zero_add 0)).v n n (add_zero n)
      (ιTensorObj (P ⊗ Q) R (i + j) k n hn
        (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z))
  simp only [cochain_comp_ofHom_apply, cochain_ofHom_comp_apply, tensorZeroCochain_apply,
    associator_apply]

lemma tensorZeroCochain_id_left {P Q Q' : Complex A} (g : Cochain Q Q' 0) :
    tensorZeroCochain (Cochain.ofHom (𝟙 P)) g = (tensorLeftHom P Q Q').f 0 g := by
  rw [tensorZeroCochain, tensorRightHom_ofHom, id_whiskerRight, Cochain.id_comp]

lemma tensorZeroCochain_id_right {P P' Q : Complex A} (f : Cochain P P' 0) :
    tensorZeroCochain f (Cochain.ofHom (𝟙 Q)) = (tensorRightHom Q P P').f 0 f := by
  rw [tensorZeroCochain, tensorLeftHom_ofHom, whiskerLeft_id, Cochain.comp_id]

end SerrePositivity.DifferentialGraded
