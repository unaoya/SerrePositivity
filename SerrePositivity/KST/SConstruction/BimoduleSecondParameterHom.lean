module
public import SerrePositivity.KST.SConstruction.RightTensorParameterFactorization
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions

/-! # 第二 tensor 因子の任意パラメータ作用と元の dg 後合成
概要：双加群の第二因子の変換は、同じ実 tensor dg 関手の全 Hom 作用と一致する。
方針：右パラメータ作用を既存右加群 Hom で表示し、全対象評価で反映する。
規約：全加群型の end は作らない。使われ方：graph 合成の左入力自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [Small.{u} B] [DGCategory A C] [Small.{u} C] [DGCategory A E]

/-- 第二因子の元の全パラメータ作用は、同じ実右 tensor Hom 写像で因子化する。 -/
lemma bimoduleSecondParam_value_factorization {K : Complex A} (P : Bimodule A B C)
    {Q Q' : Bimodule A C E} (τ : BimoduleParamTrans A C E K Q Q') (b : B) (e : E) :
    BimoduleTensor.secondParamHom A B C E P τ b e =
      τ.app e ≫ BalancedTensor.rightHomMap A C (Q.rightAt e) (Q'.rightAt e) (P.leftAt b) := by
  have h := dgRightParamHom_factorization A C (P.leftAt b)
    (Bimodule.paramRightAt A C E τ e)
  simpa only [BimoduleTensor.secondParamHom, BimoduleTensor.secondParamValue,
    Bimodule.paramRightAt, Equiv.symm_apply_apply] using h

/-- 第二因子の作用は、元の実 tensor dg 関手の同じ全 Hom の後合成。 -/
lemma bimoduleSecondParam_postcomposition {K : Complex A} (P : Bimodule A B C)
    {Q Q' : Bimodule A C E} (τ : BimoduleParamTrans A C E K Q Q') (e : E) :
    (BimoduleTensor.secondParam A B C E P τ).app e =
      τ.app e ≫ (BimoduleTensor.compose A B C (RightModule A C) P
        (DGFunctor.id (RightModule A C))).toFunctor.map (Q.rightAt e) (Q'.rightAt e) := by
  apply moduleHom_ext
  intro b
  change Bimodule.paramValue A B E (BimoduleTensor.secondParam A B C E P τ) b e = _
  rw [BimoduleTensor.secondParam_value]
  have h := BimoduleTensor.compose_leftMap_π A B C (RightModule A C) P
    (DGFunctor.id (RightModule A C)) (Q.rightAt e) (Q'.rightAt e) b
  simp only [DGFunctor.id, EnrichedFunctor.id_map, Category.id_comp] at h
  rw [Category.assoc]
  erw [h]
  exact bimoduleSecondParam_value_factorization A B C E P τ b e

end SerrePositivity.KST.SConstruction
