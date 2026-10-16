module
public import SerrePositivity.DifferentialGraded.Complexes.AssociatorCochainNaturality

/-! # tensor合成の結合図式と純tensor成分式の往復 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex
variable {A : Type u} [CommRing A]

lemma tensorComposition_assoc_apply (P Q R U V W : Complex A)
    (f : P ⊗ Q ⟶ U) (g : U ⊗ R ⟶ W) (h : Q ⊗ R ⟶ V) (k : P ⊗ V ⟶ W)
    (ha : (f ▷ R) ≫ g = (α_ P Q R).hom ≫ P ◁ h ≫ k)
    (p q r n : ℤ) (hn : p + q + r = n) (a : P.X p) (b : Q.X q) (c : R.X r) :
    g.f n (ιTensorObj U R (p + q) r n hn
      (f.f (p + q) (ιTensorObj P Q p q (p + q) rfl (a ⊗ₜ[A] b)) ⊗ₜ[A] c)) =
    k.f n (ιTensorObj P V p (q + r) n (by omega)
      (a ⊗ₜ[A] h.f (q + r) (ιTensorObj Q R q r (q + r) rfl (b ⊗ₜ[A] c)))) := by
  have hh := congrArg (fun F : (P ⊗ Q) ⊗ R ⟶ W =>
    F.f n (ιTensorObj (P ⊗ Q) R (p + q) r n hn
      (ιTensorObj P Q p q (p + q) rfl (a ⊗ₜ[A] b) ⊗ₜ[A] c))) ha
  simpa only [chain_comp_apply, whiskerRight_apply, associator_apply, whiskerLeft_apply] using hh

lemma tensorComposition_assoc_of_apply (P Q R U V W : Complex A)
    (f : P ⊗ Q ⟶ U) (g : U ⊗ R ⟶ W) (h : Q ⊗ R ⟶ V) (k : P ⊗ V ⟶ W)
    (ha : ∀ (p q r n : ℤ) (hn : p + q + r = n) (a : P.X p) (b : Q.X q) (c : R.X r),
      g.f n (ιTensorObj U R (p + q) r n hn
        (f.f (p + q) (ιTensorObj P Q p q (p + q) rfl (a ⊗ₜ[A] b)) ⊗ₜ[A] c)) =
      k.f n (ιTensorObj P V p (q + r) n (by omega)
        (a ⊗ₜ[A] h.f (q + r) (ιTensorObj Q R q r (q + r) rfl (b ⊗ₜ[A] c))))) :
    (f ▷ R) ≫ g = (α_ P Q R).hom ≫ P ◁ h ≫ k := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply SerrePositivity.cochainTensorTriple_hom_ext P Q R n
  intro p q r hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro a b c
  change g.f n ((f ▷ R).f n (ιTensorObj (P ⊗ Q) R (p + q) r n hn
      (ιTensorObj P Q p q (p + q) rfl (a ⊗ₜ[A] b) ⊗ₜ[A] c))) =
    k.f n ((P ◁ h).f n ((α_ P Q R).hom.f n (ιTensorObj (P ⊗ Q) R (p + q) r n hn
      (ιTensorObj P Q p q (p + q) rfl (a ⊗ₜ[A] b) ⊗ₜ[A] c))))
  rw [whiskerRight_apply, associator_apply, whiskerLeft_apply]
  exact ha p q r n hn a b c

end SerrePositivity.DifferentialGraded
