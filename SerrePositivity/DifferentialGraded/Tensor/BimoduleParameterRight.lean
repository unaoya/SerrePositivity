module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleParameterElements
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleRightElements

/-! # 任意パラメータの相対tensor作用と外側の右dg作用 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]
variable {K : Complex A}

lemma secondParamHom_right_cochain (P : Bimodule A B C) {Q Q' : Bimodule A C E}
    (τ : BimoduleParamTrans A C E K Q Q') (b b' : Bᵒᵖ) (e : E)
    {k p m : ℤ} (hm : k + p = m) (t : K.X k) (f : GradedHom A b b' p) :
    (((((compose A B C E P Q).rightAt e).map b b').f p f).comp
      ((secondParamHom A B C E P τ b'.unop e).f k t) (by omega)) =
    (k * p).negOnePow • (((secondParamHom A B C E P τ b.unop e).f k t).comp
      ((((compose A B C E P Q').rightAt e).map b b').f p f) hm) := by
  apply BalancedTensor.cochain_element_ext A C (Q.rightAt e) (P.leftAt b.unop)
  intro c r s i n hi hn q v
  rw [Cochain.comp_v _ _ (by omega) i (i + p) n rfl (by omega),
    Cochain.units_smul_v, Cochain.comp_v _ _ hm i (i + k) n rfl (by omega)]
  change (((secondParamHom A B C E P τ b'.unop e).f k t).v (i + p) n (by omega))
      (moduleAction A ((compose A B C E P Q).rightAt e) f
        (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b.unop) c q v hi) rfl) =
    (k * p).negOnePow • moduleAction A ((compose A B C E P Q').rightAt e) f
      ((((secondParamHom A B C E P τ b.unop e).f k t).v i (i + k) rfl)
        (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b.unop) c q v hi)) (by omega)
  rw [compose_rightAction_element A B C E P Q b b' c e
    (j := s + p) hi rfl rfl f q v]
  simp only [Units.smul_def, map_zsmul]
  rw [secondParamHom_element, secondParamHom_element,
    compose_rightAction_element A B C E P Q' b b' c e
      (j := s + p) (by omega) rfl (by omega) f]
  simp only [← Units.smul_def, smul_smul, ← Int.negOnePow_add]
  have hs : k * p + p * (k + r) = p * r + 2 * (k * p) := by ring
  rw [hs, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

lemma firstParamHom_right_cochain {P P' : Bimodule A B C} (Q : Bimodule A C E)
    (τ : BimoduleParamTrans A B C K P P') (b b' : Bᵒᵖ) (e : E)
    {k p m : ℤ} (hm : k + p = m) (t : K.X k) (f : GradedHom A b b' p) :
    (((((compose A B C E P Q).rightAt e).map b b').f p f).comp
      ((firstParamHom A B C E Q τ b'.unop e).f k t) (by omega)) =
    (k * p).negOnePow • (((firstParamHom A B C E Q τ b.unop e).f k t).comp
      ((((compose A B C E P' Q).rightAt e).map b b').f p f) hm) := by
  apply BalancedTensor.cochain_element_ext A C (Q.rightAt e) (P.leftAt b.unop)
  intro c r s i n hi hn q v
  rw [Cochain.comp_v _ _ (by omega) i (i + p) n rfl (by omega),
    Cochain.units_smul_v, Cochain.comp_v _ _ hm i (i + k) n rfl (by omega)]
  change (((firstParamHom A B C E Q τ b'.unop e).f k t).v (i + p) n (by omega))
      (moduleAction A ((compose A B C E P Q).rightAt e) f
        (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b.unop) c q v hi) rfl) =
    (k * p).negOnePow • moduleAction A ((compose A B C E P' Q).rightAt e) f
      ((((firstParamHom A B C E Q τ b.unop e).f k t).v i (i + k) rfl)
        (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b.unop) c q v hi)) (by omega)
  rw [compose_rightAction_element A B C E P Q b b' c e
    (j := s + p) hi rfl rfl f q v]
  simp only [Units.smul_def, map_zsmul]
  rw [firstParamHom_element, firstParamHom_element]
  simp only [Units.smul_def]
  have ht := moduleParamNaturality_apply_of_sum A
    (Bimodule.paramRightAt A B C τ c).app (Bimodule.paramRightAt A B C τ c).naturality
    (m := k + p) (n := k + (s + p)) (l := k + s) t f v rfl (by omega) rfl (by omega)
  change (((Bimodule.paramValue A B C τ b'.unop c).f k t).v (s + p)
      (k + (s + p)) (by omega)) (moduleAction A (P.rightAt c) f v rfl) =
    (k * p).negOnePow • moduleAction A (P'.rightAt c) f
      ((((Bimodule.paramValue A B C τ b.unop c).f k t).v s (k + s) (by omega)) v)
      (by omega) at ht
  rw [ht]
  simp only [← Units.smul_def]
  rw [param_rightAction_units_smul]
  rw [compose_rightAction_element A B C E P' Q b b' c e
    (j := k + (s + p)) (by omega) (by omega) (by omega) f]
  rw [BalancedTensor.element_units_smul_right]
  simp only [smul_smul, ← Int.negOnePow_add]
  congr 1
  congr 1
  ring

/-- 前の合成因子の変換を、全Hom自然な右B加群変換へ束ねる。 -/
def firstParamRightAt {P P' : Bimodule A B C} (Q : Bimodule A C E)
    (τ : BimoduleParamTrans A B C K P P') (e : E) :
    ModuleParamTrans A B K ((compose A B C E P Q).rightAt e)
      ((compose A B C E P' Q).rightAt e) where
  app b := firstParamHom A B C E Q τ b.unop e
  naturality := moduleParamNaturality_of_cochain A _
    (fun b b' _k _p _m hm t f => firstParamHom_right_cochain A B C E Q τ b b' e hm t f)

/-- 後の合成因子の変換を、全Hom自然な右B加群変換へ束ねる。 -/
def secondParamRightAt (P : Bimodule A B C) {Q Q' : Bimodule A C E}
    (τ : BimoduleParamTrans A C E K Q Q') (e : E) :
    ModuleParamTrans A B K ((compose A B C E P Q).rightAt e)
      ((compose A B C E P Q').rightAt e) where
  app b := secondParamHom A B C E P τ b.unop e
  naturality := moduleParamNaturality_of_cochain A _
    (fun b b' _k _p _m hm t f => secondParamHom_right_cochain A B C E P τ b b' e hm t f)

end SerrePositivity.DifferentialGraded.BimoduleTensor
