module
public import SerrePositivity.KST.SConstruction.DGModuleExtensionCompositionFactor
public import SerrePositivity.KST.SConstruction.DGModuleExtensionParameterWhiskering
public import SerrePositivity.KST.SConstruction.TensorAssociatorParameterConjugation
public import SerrePositivity.KST.SConstruction.DGGraphCompositionInputNaturality

/-! # 元の実加群延長の合成比較の全入力自然性
概要：任意 K の入力自然変換は、元の実加群延長の合成比較と全 Hom で可換である。
方針：元の比較を逆結合と tensor graph 比較へ分解し、同じ二つの共役を合成する。
規約：元の比較・入力成分・実 tensor を保つ。使われ方：実 Perf と厳密豊穣 K。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) (T : Type z)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  [DGCategory A T] [Small.{u} T]

/-- 左入力の元の全次数作用は、同じ実延長合成比較の共役後に後合成を回収する。 -/
lemma dgModuleExtensionComposition_parameter_post {K : Complex A}
    {F F' : DGFunctor A D E} (G : DGFunctor A E T)
    (τ : DGFunctorParamTrans A D E K F F') (M : RightModule A D) :
    ((dgModuleExtensionParameter A D E τ).app M ≫ (dgModuleExtension A E T G).map
        ((dgModuleExtension A D E F).obj M) ((dgModuleExtension A D E F').obj M)) ≫
        enrichedClosedIsoConjugation (Complex A) (dgModuleExtensionCompositionAt A D E T F G M)
          (dgModuleExtensionCompositionAt A D E T F' G M) =
      (dgModuleExtensionParameter A D T (dgFunctorParamPost A D E T G τ)).app M := by
  have ha := bimoduleAssociator_middleParam_inverse_conjugation A T E D (RightModule A D)
    (functorGraph A E T G) (DGFunctor.id _) (dgFunctorGraphParameter A D E τ) M
  have hg := bimoduleFirstParam_conjugation A T D (RightModule A D)
    (BimoduleTensor.secondParam A T E D (functorGraph A E T G)
      (dgFunctorGraphParameter A D E τ))
    (dgFunctorGraphParameter A D T (dgFunctorParamPost A D E T G τ))
    (dgFunctorGraphCompositionIso A D E T F G) (dgFunctorGraphCompositionIso A D E T F' G)
    (dgFunctorGraphComposition_parameter_post A D E T G τ) (DGFunctor.id _) M
  have hs := congrArg (fun k => k ≫ enrichedClosedIsoConjugation (Complex A)
    (bimoduleFirstTensorIsoAt A T D (RightModule A D) (DGFunctor.id _)
      (dgFunctorGraphCompositionIso A D E T F G) M)
    (bimoduleFirstTensorIsoAt A T D (RightModule A D) (DGFunctor.id _)
      (dgFunctorGraphCompositionIso A D E T F' G) M)) ha
  simp only [Category.assoc] at hs
  rw [enrichedClosedIsoConjugation_trans] at hs
  rw [dgModuleExtensionCompositionAt_factor, dgModuleExtensionCompositionAt_factor,
    ← dgModuleExtensionParameter_post_action]
  exact hs.trans hg

/-- 右入力の元の全次数作用は、同じ実延長合成比較の共役後に前合成を回収する。 -/
lemma dgModuleExtensionComposition_parameter_pre {K : Complex A}
    {G G' : DGFunctor A E T} (F : DGFunctor A D E)
    (τ : DGFunctorParamTrans A E T K G G') (M : RightModule A D) :
    (dgModuleExtensionParameter A E T τ).app ((dgModuleExtension A D E F).obj M) ≫
        enrichedClosedIsoConjugation (Complex A) (dgModuleExtensionCompositionAt A D E T F G M)
          (dgModuleExtensionCompositionAt A D E T F G' M) =
      (dgModuleExtensionParameter A D T (dgFunctorParamPre A E T D F τ)).app M := by
  have ha := bimoduleAssociator_firstParam_inverse_conjugation A T E D (RightModule A D)
    (functorGraph A D E F) (DGFunctor.id _) (dgFunctorGraphParameter A E T τ) M
  have hg := bimoduleFirstParam_conjugation A T D (RightModule A D)
    (BimoduleTensor.firstParam A T E D (functorGraph A D E F)
      (dgFunctorGraphParameter A E T τ))
    (dgFunctorGraphParameter A D T (dgFunctorParamPre A E T D F τ))
    (dgFunctorGraphCompositionIso A D E T F G) (dgFunctorGraphCompositionIso A D E T F G')
    (dgFunctorGraphComposition_parameter_pre A D E T F τ) (DGFunctor.id _) M
  have hs := congrArg (fun k => k ≫ enrichedClosedIsoConjugation (Complex A)
    (bimoduleFirstTensorIsoAt A T D (RightModule A D) (DGFunctor.id _)
      (dgFunctorGraphCompositionIso A D E T F G) M)
    (bimoduleFirstTensorIsoAt A T D (RightModule A D) (DGFunctor.id _)
      (dgFunctorGraphCompositionIso A D E T F G') M)) ha
  simp only [Category.assoc] at hs
  rw [enrichedClosedIsoConjugation_trans] at hs
  rw [dgModuleExtensionCompositionAt_factor, dgModuleExtensionCompositionAt_factor,
    ← dgModuleExtensionParameter_pre_action]
  exact hs.trans hg

end SerrePositivity.KST.SConstruction
