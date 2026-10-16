module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleParameterElements
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleElements
public import SerrePositivity.DifferentialGraded.Module.LeftParamNaturality

/-! # 任意パラメータの相対tensor作用と外側の左dg作用 -/
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

lemma firstParamHom_left_cochain {P P' : Bimodule A B C} (Q : Bimodule A C E)
    (τ : BimoduleParamTrans A B C K P P') (b : B) (e e' : E)
    {k p m : ℤ} (hm : k + p = m) (t : K.X k) (f : GradedHom A e e' p) :
    (((((compose A B C E P Q).leftAt b).map e e').f p f).comp
      ((firstParamHom A B C E Q τ b e').f k t) (by omega)) =
    (k * p).negOnePow • (((firstParamHom A B C E Q τ b e).f k t).comp
      ((((compose A B C E P' Q).leftAt b).map e e').f p f) hm) := by
  apply BalancedTensor.cochain_element_ext A C (Q.rightAt e) (P.leftAt b)
  intro c r s i n hi hn q v
  rw [Cochain.comp_v _ _ (by omega) i (i + p) n rfl (by omega),
    Cochain.units_smul_v, Cochain.comp_v _ _ hm i (i + k) n rfl (by omega)]
  change (((firstParamHom A B C E Q τ b e').f k t).v (i + p) n (by omega))
      (leftAction A ((compose A B C E P Q).leftAt b) f
        (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v hi) rfl) =
    (k * p).negOnePow • leftAction A ((compose A B C E P' Q).leftAt b) f
      ((((firstParamHom A B C E Q τ b e).f k t).v i (i + k) rfl)
        (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v hi)) (by omega)
  rw [compose_leftAction_element A B C E P Q b c e e'
    (j := r + p) hi rfl rfl f q v, firstParamHom_element, firstParamHom_element]
  rw [param_leftAction_units_smul]
  rw [compose_leftAction_element A B C E P' Q b c e e'
    (j := r + p) (by omega) rfl (by omega) f]
  simp only [smul_smul, ← Int.negOnePow_add]
  congr 1
  congr 1
  ring

lemma secondParamHom_left_cochain (P : Bimodule A B C) {Q Q' : Bimodule A C E}
    (τ : BimoduleParamTrans A C E K Q Q') (b : B) (e e' : E)
    {k p m : ℤ} (hm : k + p = m) (t : K.X k) (f : GradedHom A e e' p) :
    (((((compose A B C E P Q).leftAt b).map e e').f p f).comp
      ((secondParamHom A B C E P τ b e').f k t) (by omega)) =
    (k * p).negOnePow • (((secondParamHom A B C E P τ b e).f k t).comp
      ((((compose A B C E P Q').leftAt b).map e e').f p f) hm) := by
  apply BalancedTensor.cochain_element_ext A C (Q.rightAt e) (P.leftAt b)
  intro c r s i n hi hn q v
  rw [Cochain.comp_v _ _ (by omega) i (i + p) n rfl (by omega),
    Cochain.units_smul_v, Cochain.comp_v _ _ hm i (i + k) n rfl (by omega)]
  change (((secondParamHom A B C E P τ b e').f k t).v (i + p) n (by omega))
      (leftAction A ((compose A B C E P Q).leftAt b) f
        (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v hi) rfl) =
    (k * p).negOnePow • leftAction A ((compose A B C E P Q').leftAt b) f
      ((((secondParamHom A B C E P τ b e).f k t).v i (i + k) rfl)
        (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v hi)) (by omega)
  rw [compose_leftAction_element A B C E P Q b c e e'
    (j := r + p) hi rfl rfl f q v, secondParamHom_element, secondParamHom_element]
  have ht := leftParamNaturality_apply_of_sum A
    (Bimodule.paramLeftAt A C E τ c).app (Bimodule.paramLeftAt A C E τ c).naturality
    (n := k + (r + p)) (l := k + r) t f q rfl (by omega) (by omega)
  change (((Bimodule.paramValue A C E τ c e').f k t).v (r + p)
      (k + (r + p)) (by omega)) (leftAction A (Q.leftAt c) f q rfl) =
    (k * p).negOnePow • leftAction A (Q'.leftAt c) f
      ((((Bimodule.paramValue A C E τ c e).f k t).v r (k + r) (by omega)) q)
      (by omega) at ht
  rw [ht, compose_leftAction_element A B C E P Q' b c e e'
    (j := k + (r + p)) (by omega) (by omega) (by omega) f]
  exact param_element_units_smul_left A C (Q'.rightAt e') (P.leftAt b) c
    (k * p).negOnePow _ v (by omega)

end SerrePositivity.DifferentialGraded.BimoduleTensor
