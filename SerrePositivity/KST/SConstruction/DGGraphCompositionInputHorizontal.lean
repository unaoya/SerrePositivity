module
public import SerrePositivity.KST.SConstruction.DGGraphCompositionInputNaturality
public import SerrePositivity.KST.SConstruction.DGFunctorGraphParameterComposition
public import SerrePositivity.KST.SConstruction.DGConjugationNaturality

/-! # graph 合成比較と元の全パラメータ横合成
概要：二つの入力自然変換の実 tensor 作用は、元の graph 比較による共役後に横合成を回収する。
方針：左右の全次数自然性を共役の式へ移し、中間の実同型を合成で相殺する。
規約：元の K⊗L・実 graph・合成比較を保つ。使われ方：実 Perf 延長の入力横合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) (T : Type z)
  [DGCategory A D] [DGCategory A E] [Small.{u} E] [DGCategory A T] [Small.{u} T]

/-- 左入力の元の全パラメータ作用は、元の graph 比較の共役後に後合成を回収する。 -/
lemma dgFunctorGraphComposition_parameter_post_conjugation
    {K : Complex A} {F F' : DGFunctor A D E} (G : DGFunctor A E T)
    (τ : DGFunctorParamTrans A D E K F F') (d : D) :
    (BimoduleTensor.secondParam A T E D (functorGraph A E T G)
        (dgFunctorGraphParameter A D E τ)).app d ≫
        enrichedClosedIsoConjugation (Complex A) (dgFunctorGraphCompositionAt A D E T F G d)
          (dgFunctorGraphCompositionAt A D E T F' G d) =
      (dgFunctorGraphParameter A D T (dgFunctorParamPost A D E T G τ)).app d :=
  enrichedConjugation_of_naturality (Complex A) _ _ _ _
    (dgFunctorGraphComposition_parameter_post A D E T G τ d)

/-- 右入力の元の全パラメータ作用は、元の graph 比較の共役後に前合成を回収する。 -/
lemma dgFunctorGraphComposition_parameter_pre_conjugation
    {K : Complex A} {G G' : DGFunctor A E T} (F : DGFunctor A D E)
    (τ : DGFunctorParamTrans A E T K G G') (d : D) :
    (BimoduleTensor.firstParam A T E D (functorGraph A D E F)
        (dgFunctorGraphParameter A E T τ)).app d ≫
        enrichedClosedIsoConjugation (Complex A) (dgFunctorGraphCompositionAt A D E T F G d)
          (dgFunctorGraphCompositionAt A D E T F G' d) =
      (dgFunctorGraphParameter A D T (dgFunctorParamPre A E T D F τ)).app d :=
  enrichedConjugation_of_naturality (Complex A) _ _ _ _
    (dgFunctorGraphComposition_parameter_pre A D E T F τ d)

/-- 二つの元のパラメータの実 tensor 作用は、graph 比較の共役後に横合成と一致する。 -/
lemma dgFunctorGraphComposition_parameter_horizontal {K L : Complex A}
    {F F' : DGFunctor A D E} {G G' : DGFunctor A E T}
    (a : DGFunctorParamTrans A D E K F F') (b : DGFunctorParamTrans A E T L G G') (d : D) :
    ((BimoduleTensor.secondParam A T E D (functorGraph A E T G)
          (dgFunctorGraphParameter A D E a)).app d ⊗ₘ
        (BimoduleTensor.firstParam A T E D (functorGraph A D E F')
          (dgFunctorGraphParameter A E T b)).app d) ≫
        moduleComposition A T _ _ _ ≫
          enrichedClosedIsoConjugation (Complex A) (dgFunctorGraphCompositionAt A D E T F G d)
            (dgFunctorGraphCompositionAt A D E T F' G' d) =
      (dgFunctorGraphParameter A D T (dgFunctorParamCompose A D T
        (dgFunctorParamPost A D E T G a) (dgFunctorParamPre A E T D F' b))).app d := by
  have hc := congrArg (fun k =>
    ((BimoduleTensor.secondParam A T E D (functorGraph A E T G)
        (dgFunctorGraphParameter A D E a)).app d ⊗ₘ
      (BimoduleTensor.firstParam A T E D (functorGraph A D E F')
        (dgFunctorGraphParameter A E T b)).app d) ≫ k)
    (enrichedClosedIsoConjugation_comp (Complex A) (dgFunctorGraphCompositionAt A D E T F G d)
      (dgFunctorGraphCompositionAt A D E T F' G d)
      (dgFunctorGraphCompositionAt A D E T F' G' d))
  simp only [tensorHom_comp_tensorHom_assoc] at hc
  rw [dgFunctorGraphComposition_parameter_post_conjugation,
    dgFunctorGraphComposition_parameter_pre_conjugation] at hc
  exact hc.symm.trans (dgFunctorGraphParameter_compose A D T
    (dgFunctorParamPost A D E T G a) (dgFunctorParamPre A E T D F' b) d).symm

end SerrePositivity.KST.SConstruction
