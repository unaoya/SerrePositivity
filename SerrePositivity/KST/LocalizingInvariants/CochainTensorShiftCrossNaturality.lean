module

public import SerrePositivity.KST.LocalizingInvariants.CochainTensorShiftElements

/-!
概要：shift しない側の因子に関する tensor–shift 同型の自然性。
方針：斉次 tensor 上で、再添字付けと Koszul 符号の両立を確認する。
規約：元の全 chain map の等式。使われ方：shift 後の単位・積保存の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] {P P' Q Q' : CochainComplex (ModuleCat R) ℤ}

@[reassoc]
lemma tensorShiftRight_naturality_left (f : P ⟶ P') (Q : CochainComplex (ModuleCat R) ℤ)
    (s : ℤ) :
    (f ▷ Q⟦s⟧) ≫ (cochainTensorShiftRight P' Q s).hom =
      (cochainTensorShiftRight P Q s).hom ≫ (f ▷ Q)⟦s⟧' := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change (cochainTensorShiftRight P' Q s).hom.f n
    ((cochainTensorMap f (𝟙 (Q⟦s⟧))).f n (ιTensorObj P (Q⟦s⟧) i j n h (x ⊗ₜ[R] y))) =
    (cochainTensorMap f (𝟙 Q)).f (n + s)
      ((cochainTensorShiftRight P Q s).hom.f n
        (ιTensorObj P (Q⟦s⟧) i j n h (x ⊗ₜ[R] y)))
  rw [cochainTensorMap_apply_ι, tensorShiftRight_apply, tensorShiftRight_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, Units.smul_def, map_zsmul]
  rw [cochainTensorMap_apply_ι]
  rfl

@[reassoc]
lemma tensorShiftLeft_naturality_right (P : CochainComplex (ModuleCat R) ℤ) (g : Q ⟶ Q')
    (s : ℤ) :
    (P⟦s⟧ ◁ g) ≫ (cochainTensorShiftLeft P Q' s).hom =
      (cochainTensorShiftLeft P Q s).hom ≫ (P ◁ g)⟦s⟧' := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change (cochainTensorShiftLeft P Q' s).hom.f n
    ((cochainTensorMap (𝟙 (P⟦s⟧)) g).f n (ιTensorObj (P⟦s⟧) Q i j n h (x ⊗ₜ[R] y))) =
    (cochainTensorMap (𝟙 P) g).f (n + s)
      ((cochainTensorShiftLeft P Q s).hom.f n
        (ιTensorObj (P⟦s⟧) Q i j n h (x ⊗ₜ[R] y)))
  rw [cochainTensorMap_apply_ι, tensorShiftLeft_apply, tensorShiftLeft_apply,
    cochainTensorMap_apply_ι]
  rfl

end SerrePositivity.KST.LocalizingInvariants
