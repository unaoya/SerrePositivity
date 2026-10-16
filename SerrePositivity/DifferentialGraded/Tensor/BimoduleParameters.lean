module
public import SerrePositivity.DifferentialGraded.Bimodule.ParameterFamily
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleParameterRight
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleParameterLeft

/-! # 相対tensor合成の各変数の全次数パラメータ付きbimodule変換 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]
variable {K : Complex A}

/-- 前の合成因子に作用する、任意Kパラメータの全dg自然な変換。 -/
def firstParam {P P' : Bimodule A B C} (Q : Bimodule A C E)
    (τ : BimoduleParamTrans A B C K P P') :
    BimoduleParamTrans A B E K (compose A B C E P Q) (compose A B C E P' Q) :=
  Bimodule.paramFamilyTrans A B E (firstParamRightAt A B C E Q τ)
    (fun b e e' => Bimodule.leftParamNaturality_of_cochain A
      (M := (compose A B C E P Q).leftAt b) (N := (compose A B C E P' Q).leftAt b)
      (fun d => firstParamHom A B C E Q τ b d)
      (fun d d' _k _p _m hm t f => firstParamHom_left_cochain A B C E Q τ b d d' hm t f)
      e e')

/-- 後の合成因子に作用する、任意Kパラメータの全dg自然な変換。 -/
def secondParam (P : Bimodule A B C) {Q Q' : Bimodule A C E}
    (τ : BimoduleParamTrans A C E K Q Q') :
    BimoduleParamTrans A B E K (compose A B C E P Q) (compose A B C E P Q') :=
  Bimodule.paramFamilyTrans A B E (secondParamRightAt A B C E P τ)
    (fun b e e' => Bimodule.leftParamNaturality_of_cochain A
      (M := (compose A B C E P Q).leftAt b) (N := (compose A B C E P Q').leftAt b)
      (fun d => secondParamHom A B C E P τ b d)
      (fun d d' _k _p _m hm t f => secondParamHom_left_cochain A B C E P τ b d d' hm t f)
      e e')

@[simp]
lemma firstParam_value {P P' : Bimodule A B C} (Q : Bimodule A C E)
    (τ : BimoduleParamTrans A B C K P P') (b : B) (e : E) :
    Bimodule.paramValue A B E (firstParam A B C E Q τ) b e =
      firstParamHom A B C E Q τ b e :=
  Bimodule.paramFamilyTrans_value A B E _ _ b e

@[simp]
lemma secondParam_value (P : Bimodule A B C) {Q Q' : Bimodule A C E}
    (τ : BimoduleParamTrans A C E K Q Q') (b : B) (e : E) :
    Bimodule.paramValue A B E (secondParam A B C E P τ) b e =
      secondParamHom A B C E P τ b e :=
  Bimodule.paramFamilyTrans_value A B E _ _ b e

end SerrePositivity.DifferentialGraded.BimoduleTensor
