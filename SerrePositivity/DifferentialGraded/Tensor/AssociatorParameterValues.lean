module
public import SerrePositivity.DifferentialGraded.Tensor.TripleParameterRest
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorParameterExt
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorValueHom
public import SerrePositivity.DifferentialGraded.Complexes.UnitScalarEvaluation

/-! # 結合比較の各bimodule変数に関する任意パラメータ自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]
variable {K : Complex A}

lemma associator_firstParam_value {P P' : Bimodule A B C} (Q : Bimodule A C E)
    (R : Bimodule A E F) (τ : BimoduleParamTrans A B C K P P') (b : B) (f : F) :
    firstParamHom A B E F R (firstParam A B C E Q τ) b f ≫
      homPostcompose _ (associatorValueHom A B C E F P' Q R b f) =
    firstParamHom A B C F (compose A C E F Q R) τ b f ≫
      homPrecompose (associatorValueHom A B C E F P Q R b f) _ := by
  apply associatorLeft_homMap_post_pre_eq A B C E F P Q R b f
  intro p x c e k r s i m n hi hm hn t q v
  rw [tripleFirstLeft_element, chain_units_smul, chain_units_smul]
  have hL := associatorValueComponent_element A B C E F P' Q R b c e f
    (i := p + i) (l := k + r) (n := n) t q
    ((((Bimodule.paramValue A B C τ b c).f p x).v s (p + s) (by omega)) v)
    (by omega) rfl (by omega)
  have hR := associatorValueComponent_element A B C E F P Q R b c e f
    (l := k + r) t q v hi rfl hm
  rw [associatorValueHom_apply, hL, associatorValueHom_apply, hR, tripleFirstRight_element]
  rw [smul_smul, ← Int.negOnePow_add]
  congr 1
  congr 1
  ring

lemma associator_middleParam_value (P : Bimodule A B C) {Q Q' : Bimodule A C E}
    (R : Bimodule A E F) (τ : BimoduleParamTrans A C E K Q Q') (b : B) (f : F) :
    firstParamHom A B E F R (secondParam A B C E P τ) b f ≫
      homPostcompose _ (associatorValueHom A B C E F P Q' R b f) =
    secondParamHom A B C F P (firstParam A C E F R τ) b f ≫
      homPrecompose (associatorValueHom A B C E F P Q R b f) _ := by
  apply associatorLeft_homMap_post_pre_eq A B C E F P Q R b f
  intro p x c e k r s i m n hi hm hn t q v
  rw [tripleMiddleLeft_element, chain_units_smul]
  have hL := associatorValueComponent_element A B C E F P Q' R b c e f
    (i := p + i) (l := p + (k + r)) (n := n) t
    ((((Bimodule.paramValue A C E τ c e).f p x).v r (p + r) (by omega)) q) v
    (by omega) (by omega) (by omega)
  have hR := associatorValueComponent_element A B C E F P Q R b c e f
    (l := k + r) t q v hi rfl hm
  rw [associatorValueHom_apply, hL, associatorValueHom_apply, hR,
    tripleMiddleRight_element]

lemma associator_lastParam_value (P : Bimodule A B C) (Q : Bimodule A C E)
    {R R' : Bimodule A E F} (τ : BimoduleParamTrans A E F K R R') (b : B) (f : F) :
    secondParamHom A B E F (compose A B C E P Q) τ b f ≫
      homPostcompose _ (associatorValueHom A B C E F P Q R' b f) =
    secondParamHom A B C F P (secondParam A C E F Q τ) b f ≫
      homPrecompose (associatorValueHom A B C E F P Q R b f) _ := by
  apply associatorLeft_homMap_post_pre_eq A B C E F P Q R b f
  intro p x c e k r s i m n hi hm hn t q v
  rw [tripleLastLeft_element]
  have hL := associatorValueComponent_element A B C E F P Q R' b c e f
    (i := i) (l := p + (k + r)) (n := n)
    ((((Bimodule.paramValue A E F τ e f).f p x).v k (p + k) (by omega)) t) q v
    hi (by omega) (by omega)
  have hR := associatorValueComponent_element A B C E F P Q R b c e f
    (l := k + r) t q v hi rfl hm
  rw [associatorValueHom_apply, hL, associatorValueHom_apply, hR, tripleLastRight_element]

end SerrePositivity.DifferentialGraded.BimoduleTensor
