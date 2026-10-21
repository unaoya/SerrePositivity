module
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugHomotopyTensor
/-!
概要：実 augmentation の比較成分の斉次合成則を、豊穣順と通常順の両規約で証明する。
方針：同じ全 tensor 上の実合成比較を評価し、Koszul 符号を照合する。
規約：任意の二整数次数。使われ方：augmentation prism の高次切断和。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory HomologicalComplex
  CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y Z : DGFunctorCommaObject R C E F)
  (p q : ℤ) (a : GradedHom R X Y p) (b : GradedHom R Y Z q)
/-- 豊穣順の比較合成則の符号は、最初に作用する斉次射の次数 p。 -/
lemma dgCommaAugmentationHomotopyComponent_forward :
    dgCommaAugmentationHomotopyComponent R C E F X Z (p + q) (forward R a b rfl) =
      forward R (x := X.replacement) (y := F.obj Y.source) (z := F.obj Z.source)
        (dgCommaAugmentationHomotopyComponent R C E F X Y p a)
        ((dgFunctorCommaImageHomMap R C E F Y Z).f q b) (by omega) +
      p.negOnePow • forward R
        (x := X.replacement) (y := Y.replacement) (z := F.obj Z.source)
        ((dgFunctorCommaReplacementHomMap R C E F X Y).f p a)
        (dgCommaAugmentationHomotopyComponent R C E F Y Z q b) (by omega) := by
  have he := Cochain.congr_v (dgFunctorCommaComposition_comparison R C E F X Y Z)
    (p + q) (p + q - 1) (by omega)
  have ht := ConcreteCategory.congr_hom he
    (ιTensorObj (homObject R _ X Y) (homObject R _ Y Z) p q (p + q) rfl (a ⊗ₜ[R] b))
  simp only [dgFunctorCommaHomComparison, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, dgFunctorCommaCompositePrimitive, Cochain.add_v,
    ModuleCat.comp_apply, ModuleCat.hom_add, LinearMap.add_apply] at ht
  change dgCommaAugmentationHomotopyComponent R C E F X Z (p + q) (forward R a b rfl) =
    (dgFunctorCommaFirstCompositePrimitive R C E F X Y Z).v
      (p + q) (p + q - 1) (by omega)
      (ιTensorObj (homObject R _ X Y) (homObject R _ Y Z) p q (p + q) rfl (a ⊗ₜ[R] b)) +
    (dgFunctorCommaSecondCompositePrimitive R C E F X Y Z).v
      (p + q) (p + q - 1) (by omega)
      (ιTensorObj (homObject R _ X Y) (homObject R _ Y Z) p q (p + q) rfl (a ⊗ₜ[R] b)) at ht
  rw [dgCommaAugmentationHomotopy_firstTensor_apply,
    dgCommaAugmentationHomotopy_secondTensor_apply] at ht
  exact ht
/-- 通常順の比較合成則の符号は、後に作用する斉次射の次数 q。 -/
lemma dgCommaAugmentationHomotopyComponent_compose :
    dgCommaAugmentationHomotopyComponent R C E F X Z (p + q) (compose R b a rfl) =
      q.negOnePow • compose R
        (x := X.replacement) (y := F.obj Y.source) (z := F.obj Z.source)
        ((dgFunctorCommaImageHomMap R C E F Y Z).f q b)
        (dgCommaAugmentationHomotopyComponent R C E F X Y p a) (by omega) +
      compose R (x := X.replacement) (y := Y.replacement) (z := F.obj Z.source)
        (dgCommaAugmentationHomotopyComponent R C E F Y Z q b)
        ((dgFunctorCommaReplacementHomMap R C E F X Y).f p a) (by omega) := by
  simp only [compose, dgCommaAugmentationHomotopyComponent_units_smul,
    dgCommaAugmentationHomotopyComponent_forward, smul_add, smul_smul,
    ← Int.negOnePow_add]
  have h₁ : q + (p - 1) * q = p * q := by ring
  have h₂ : (p * q + p).negOnePow = (p * (q - 1)).negOnePow := by
    rw [show p * q + p = p * (q - 1) + 2 * p by ring,
      Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]
  rw [h₁, h₂]
end SerrePositivity.InfinityCategories
