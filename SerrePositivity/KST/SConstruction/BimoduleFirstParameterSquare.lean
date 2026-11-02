module
public import SerrePositivity.KST.SConstruction.BimoduleParameterSquareValues
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions


public import SerrePositivity.DifferentialGraded.Tensor.BalancedElements
public import SerrePositivity.DifferentialGraded.Complexes.UnitScalarEvaluation

/-! # 実 tensor による全パラメータ可換四角形の保存
概要：第一因子に関する任意 K の可換四角形は、元の相対 tensor の下でも可換。
方針：全次数の純 coend 生成元で、同じ交差符号と元の値の四角形を回収する。
規約：元の閉零 tensor 射と全パラメータ作用を保つ。使われ方：graph 比較の実延長。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [Small.{u} B] [DGCategory A C] [Small.{u} C] [DGCategory A E]
variable {K : Complex A} {P P' N N' : BimoduleCategory A B C}
  (τ : BimoduleParamTrans A B C K (BimoduleCategory.underlying A B C P)
    (BimoduleCategory.underlying A B C P'))
  (υ : BimoduleParamTrans A B C K (BimoduleCategory.underlying A B C N)
    (BimoduleCategory.underlying A B C N')) (f : P ⟶ N) (g : P' ⟶ N') (Q : Bimodule A C E)
local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "P₁" => BimoduleCategory.underlying A B C P'
local notation "N₀" => BimoduleCategory.underlying A B C N
local notation "N₁" => BimoduleCategory.underlying A B C N'

/-- 元の値の四角形は、同じ実 tensor の全 Hom 値の四角形を与える。 -/
lemma bimoduleFirstParam_square_value
    (h : ∀ b c, Bimodule.paramValue A B C τ b c ≫
      homPostcompose ((P₀).value b c) ((BimoduleCategory.valueEvaluation A B C b c).map g) =
      Bimodule.paramValue A B C υ b c ≫
        homPrecompose ((BimoduleCategory.valueEvaluation A B C b c).map f) ((N₁).value b c))
    (b : B) (e : E) :
    BimoduleTensor.firstParamHom A B C E Q τ b e ≫
        homPostcompose ((BimoduleTensor.compose A B C E P₀ Q).value b e)
          (BimoduleTensor.composeValueMap A B C E g (𝟙 (BimoduleCategory.of A C E Q)) b e) =
      BimoduleTensor.firstParamHom A B C E Q υ b e ≫
        homPrecompose
          (BimoduleTensor.composeValueMap A B C E f (𝟙 (BimoduleCategory.of A C E Q)) b e)
          ((BimoduleTensor.compose A B C E N₁ Q).value b e) := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (homPostcompose _ _).f p
      ((BimoduleTensor.firstParamHom A B C E Q τ b e).f p x) =
    (homPrecompose _ _).f p ((BimoduleTensor.firstParamHom A B C E Q υ b e).f p x)
  rw [homPostcompose_apply, homPrecompose_apply]
  apply BalancedTensor.cochain_element_ext A C (Q.rightAt e) ((P₀).leftAt b)
  intro c r s i n hi hn q v
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.ofHom_v]
  have hv := congrArg (fun k => ((k.f p x).v s (p + s) (by omega)) v) (h b c)
  change ((homPostcompose _ _).f p ((Bimodule.paramValue A B C τ b c).f p x)).v
      s (p + s) (by omega) v =
    ((homPrecompose _ _).f p ((Bimodule.paramValue A B C υ b c).f p x)).v
      s (p + s) (by omega) v at hv
  rw [homPostcompose_apply, homPrecompose_apply, Cochain.comp_zero_cochain_v,
    Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.ofHom_v] at hv
  simp only [ModuleCat.comp_apply] at hv ⊢
  erw [BimoduleTensor.firstParamHom_element, chain_units_smul,
    BimoduleTensor.composeValueMap_element, BimoduleTensor.composeValueMap_element]
  simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ModuleCat.id_apply]
  erw [BimoduleTensor.firstParamHom_element, hv]
  rfl

/-- 元の第一因子の K 四角形は、実 tensor の全加群 Hom でも可換のまま。 -/
lemma bimoduleFirstParam_square
    (h : ∀ c, τ.app c ≫ moduleHomPostcompose A B _ _ _ (g.val c) =
      υ.app c ≫ moduleHomPrecompose A B _ _ _ (f.val c)) (e : E) :
    (BimoduleTensor.firstParam A B C E Q τ).app e ≫
        moduleHomPostcompose A B
          ((BimoduleTensor.compose A B C E P₀ Q).rightAt e)
          ((BimoduleTensor.compose A B C E P₁ Q).rightAt e)
          ((BimoduleTensor.compose A B C E N₁ Q).rightAt e)
          (BimoduleTensor.composeRightMap A B C E g (𝟙 (BimoduleCategory.of A C E Q)) e) =
      (BimoduleTensor.firstParam A B C E Q υ).app e ≫
        moduleHomPrecompose A B
          ((BimoduleTensor.compose A B C E P₀ Q).rightAt e)
          ((BimoduleTensor.compose A B C E N₀ Q).rightAt e)
          ((BimoduleTensor.compose A B C E N₁ Q).rightAt e)
          (BimoduleTensor.composeRightMap A B C E f (𝟙 (BimoduleCategory.of A C E Q)) e) := by
  apply Bimodule.param_square_of_values A B E
    (BimoduleTensor.firstParam A B C E Q τ) (BimoduleTensor.firstParam A B C E Q υ)
    (fun e => BimoduleTensor.composeRightMap A B C E f (𝟙 (BimoduleCategory.of A C E Q)) e)
    (fun e => BimoduleTensor.composeRightMap A B C E g (𝟙 (BimoduleCategory.of A C E Q)) e)
  intro b e
  simp only [BimoduleTensor.firstParam_value]
  erw [BimoduleTensor.composeRightMap_component, BimoduleTensor.composeRightMap_component]
  rw [BimoduleTensor.composeValueHom_eq, BimoduleTensor.composeValueHom_eq]
  exact bimoduleFirstParam_square_value A B C E τ υ f g Q
    (bimoduleParameter_square_value A B C τ υ f g h) b e

end SerrePositivity.KST.SConstruction
