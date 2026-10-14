module

public import SerrePositivity.PerfectComplex.TensorSixShuffle

/-! # Homogeneous generators for the six-factor cochain tensor -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
variable {R : Type u} [CommRing R]

lemma cochainTensorX_whiskerRight_twice_hom_ext
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) (T U Y : ModuleCat.{u} R)
    {f g : ((cochainTensor P Q).X n ⊗ T) ⊗ U ⟶ Y}
    (h : ∀ i j (hij : i + j = n), ((ιTensorObj P Q i j n hij ▷ T) ▷ U) ≫ f =
      ((ιTensorObj P Q i j n hij ▷ T) ▷ U) ≫ g) : f = g := by
  apply (isColimitOfHasCoproductOfPreservesColimit
    (tensorRight T ⋙ tensorRight U) (cochainTensorSummand P Q n)).hom_ext
  intro ij
  exact h ij.as.val.1 ij.as.val.2 ij.as.property

lemma cochainTensorX_whiskerLeft_right_hom_ext
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) (T U Y : ModuleCat.{u} R)
    {f g : (T ⊗ (cochainTensor P Q).X n) ⊗ U ⟶ Y}
    (h : ∀ i j (hij : i + j = n), ((T ◁ ιTensorObj P Q i j n hij) ▷ U) ≫ f =
      ((T ◁ ιTensorObj P Q i j n hij) ▷ U) ≫ g) : f = g := by
  apply (isColimitOfHasCoproductOfPreservesColimit
    (tensorLeft T ⋙ tensorRight U) (cochainTensorSummand P Q n)).hom_ext
  intro ij
  exact h ij.as.val.1 ij.as.val.2 ij.as.property

lemma cochainTensorSix_hom_ext (P Q T U V W : CochainComplex (ModuleCat.{u} R) ℤ)
    (n : ℤ) {Y : ModuleCat.{u} R}
    {f g : (cochainTensor (cochainTensor (cochainTensor P Q) (cochainTensor T U))
      (cochainTensor V W)).X n ⟶ Y}
    (h : ∀ i j k l a b (hijklab : i + j + k + l + a + b = n),
      cochainTensorSixι P Q T U V W i j k l a b n hijklab ≫ f =
        cochainTensorSixι P Q T U V W i j k l a b n hijklab ≫ g) : f = g := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro s c hsc
  dsimp at hsc
  apply cochainTensorX_whiskerRight_hom_ext (cochainTensor P Q) (cochainTensor T U)
    s ((cochainTensor V W).X c) Y
  intro d e hde
  apply cochainTensorX_whiskerRight_twice_hom_ext P Q d ((cochainTensor T U).X e)
    ((cochainTensor V W).X c) Y
  intro i j hij
  apply cochainTensorX_whiskerLeft_right_hom_ext T U e (P.X i ⊗ Q.X j)
    ((cochainTensor V W).X c) Y
  intro k l hkl
  apply cochainTensorX_whiskerLeft_hom_ext V W c ((P.X i ⊗ Q.X j) ⊗ (T.X k ⊗ U.X l)) Y
  intro a b hab
  subst d
  subst e
  subst c
  have hs : s = i + j + k + l := by omega
  subst hs
  simp only [← comp_whiskerRight_assoc, ← tensorHom_def'_assoc]
  exact h i j k l a b (by omega)

/-- Six pure factors determine a linear map out of three paired tensors. -/
lemma tensorProductSix_ext_pairs
    {A B C D E F G : Type u}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]
    [Module R A] [Module R B] [Module R C] [Module R D]
    [Module R E] [Module R F] [Module R G]
    {f g : ((A ⊗[R] B) ⊗[R] (C ⊗[R] D)) ⊗[R] (E ⊗[R] F) →ₗ[R] G}
    (h : ∀ a b c d e r, f (((a ⊗ₜ[R] b) ⊗ₜ[R] (c ⊗ₜ[R] d)) ⊗ₜ[R] (e ⊗ₜ[R] r)) =
      g (((a ⊗ₜ[R] b) ⊗ₜ[R] (c ⊗ₜ[R] d)) ⊗ₜ[R] (e ⊗ₜ[R] r))) : f = g := by
  apply TensorProduct.ext'
  intro p q
  have hL : f.comp ((TensorProduct.mk R ((A ⊗[R] B) ⊗[R] (C ⊗[R] D))
      (E ⊗[R] F)).flip q) =
      g.comp ((TensorProduct.mk R ((A ⊗[R] B) ⊗[R] (C ⊗[R] D)) (E ⊗[R] F)).flip q) := by
    apply TensorProduct.ext_fourfold'
    intro a b c d
    have hR : f.comp (TensorProduct.mk R ((A ⊗[R] B) ⊗[R] (C ⊗[R] D)) (E ⊗[R] F)
        ((a ⊗ₜ[R] b) ⊗ₜ[R] (c ⊗ₜ[R] d))) =
        g.comp (TensorProduct.mk R ((A ⊗[R] B) ⊗[R] (C ⊗[R] D)) (E ⊗[R] F)
          ((a ⊗ₜ[R] b) ⊗ₜ[R] (c ⊗ₜ[R] d))) := by
      apply TensorProduct.ext'
      intro e r
      exact h a b c d e r
    exact congrArg (fun k : E ⊗[R] F →ₗ[R] G => k q) hR
  exact congrArg (fun k : (A ⊗[R] B) ⊗[R] (C ⊗[R] D) →ₗ[R] G => k p) hL

end SerrePositivity
