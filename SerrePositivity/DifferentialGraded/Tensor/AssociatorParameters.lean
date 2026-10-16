module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorParameterValues
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorBimodule
public import SerrePositivity.DifferentialGraded.Bimodule.ParameterSquare

/-! # 主Hom endにおける結合比較の三変数の任意パラメータ自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]
variable {K : Complex A}

/-- P変数の任意パラメータ変換に対する、全Hom endでの結合自然性。 -/
lemma associator_firstParam {P P' : Bimodule A B C} (Q : Bimodule A C E)
    (R : Bimodule A E F) (τ : BimoduleParamTrans A B C K P P') (f : F) :
    (firstParam A B E F R (firstParam A B C E Q τ)).app f ≫
      moduleHomPostcompose A B
        ((compose A B E F (compose A B C E P Q) R).rightAt f)
        ((compose A B E F (compose A B C E P' Q) R).rightAt f)
        ((compose A B C F P' (compose A C E F Q R)).rightAt f)
        (associatorRightModuleIso A B C E F P' Q R f).hom =
    (firstParam A B C F (compose A C E F Q R) τ).app f ≫
      moduleHomPrecompose A B
        ((compose A B E F (compose A B C E P Q) R).rightAt f)
        ((compose A B C F P (compose A C E F Q R)).rightAt f)
        ((compose A B C F P' (compose A C E F Q R)).rightAt f)
        (associatorRightModuleIso A B C E F P Q R f).hom := by
  apply Bimodule.param_square_of_values A B F
    (firstParam A B E F R (firstParam A B C E Q τ))
    (firstParam A B C F (compose A C E F Q R) τ)
    (fun d => (associatorRightModuleIso A B C E F P Q R d).hom)
    (fun d => (associatorRightModuleIso A B C E F P' Q R d).hom)
  intro b d
  simp only [firstParam_value, associatorRightModuleIso_hom_component]
  simpa only [associatorValueHom_eq] using associator_firstParam_value A B C E F Q R τ b d

/-- Q変数の任意パラメータ変換に対する、全Hom endでの結合自然性。 -/
lemma associator_middleParam (P : Bimodule A B C) {Q Q' : Bimodule A C E}
    (R : Bimodule A E F) (τ : BimoduleParamTrans A C E K Q Q') (f : F) :
    (firstParam A B E F R (secondParam A B C E P τ)).app f ≫
      moduleHomPostcompose A B
        ((compose A B E F (compose A B C E P Q) R).rightAt f)
        ((compose A B E F (compose A B C E P Q') R).rightAt f)
        ((compose A B C F P (compose A C E F Q' R)).rightAt f)
        (associatorRightModuleIso A B C E F P Q' R f).hom =
    (secondParam A B C F P (firstParam A C E F R τ)).app f ≫
      moduleHomPrecompose A B
        ((compose A B E F (compose A B C E P Q) R).rightAt f)
        ((compose A B C F P (compose A C E F Q R)).rightAt f)
        ((compose A B C F P (compose A C E F Q' R)).rightAt f)
        (associatorRightModuleIso A B C E F P Q R f).hom := by
  apply Bimodule.param_square_of_values A B F
    (firstParam A B E F R (secondParam A B C E P τ))
    (secondParam A B C F P (firstParam A C E F R τ))
    (fun d => (associatorRightModuleIso A B C E F P Q R d).hom)
    (fun d => (associatorRightModuleIso A B C E F P Q' R d).hom)
  intro b d
  simp only [firstParam_value, secondParam_value, associatorRightModuleIso_hom_component]
  simpa only [associatorValueHom_eq] using associator_middleParam_value A B C E F P R τ b d

/-- R変数の任意パラメータ変換に対する、全Hom endでの結合自然性。 -/
lemma associator_lastParam (P : Bimodule A B C) (Q : Bimodule A C E)
    {R R' : Bimodule A E F} (τ : BimoduleParamTrans A E F K R R') (f : F) :
    (secondParam A B E F (compose A B C E P Q) τ).app f ≫
      moduleHomPostcompose A B
        ((compose A B E F (compose A B C E P Q) R).rightAt f)
        ((compose A B E F (compose A B C E P Q) R').rightAt f)
        ((compose A B C F P (compose A C E F Q R')).rightAt f)
        (associatorRightModuleIso A B C E F P Q R' f).hom =
    (secondParam A B C F P (secondParam A C E F Q τ)).app f ≫
      moduleHomPrecompose A B
        ((compose A B E F (compose A B C E P Q) R).rightAt f)
        ((compose A B C F P (compose A C E F Q R)).rightAt f)
        ((compose A B C F P (compose A C E F Q R')).rightAt f)
        (associatorRightModuleIso A B C E F P Q R f).hom := by
  apply Bimodule.param_square_of_values A B F
    (secondParam A B E F (compose A B C E P Q) τ)
    (secondParam A B C F P (secondParam A C E F Q τ))
    (fun d => (associatorRightModuleIso A B C E F P Q R d).hom)
    (fun d => (associatorRightModuleIso A B C E F P Q R' d).hom)
  intro b d
  simp only [secondParam_value, associatorRightModuleIso_hom_component]
  simpa only [associatorValueHom_eq] using associator_lastParam_value A B C E F P Q τ b d

end SerrePositivity.DifferentialGraded.BimoduleTensor
