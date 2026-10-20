module
public import SerrePositivity.KST.SConstruction.DGModuleExtensionComposition
public import SerrePositivity.KST.SConstruction.DGModuleExtensionUnitTensor
public import SerrePositivity.KST.SConstruction.DGFunctorGraphUnits
public import SerrePositivity.DifferentialGraded.Tensor.Triangle

/-! # 元の実 graph 延長の単位三角
概要：恒等入力との実合成比較を、元の全加群上の単位比較と照合する。
方針：graph 単位の回収と tensor の三角を、等号移送を保って合成する。
規約：対象別の等号で全 Hom 自然性を代用しない。使われ方：Perf 比較の三角整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]

/-- 対角の等号移送を保った、全加群を左パラメータとする元の tensor 三角。 -/
lemma dgDiagonalTensorUnit_triangle (P : Bimodule A E D) (Q : Bimodule A D D)
    (h : Q = Bimodule.diagonal A D) :
    (BimoduleTensor.associatorIso A E D D (RightModule A D) P Q (DGFunctor.id _)).inv ≫
        (dgModuleGraphTensorFunctor A D E).map
          ((eqToIso (congrArg (fun R => BimoduleCategory.of A E D
              (BimoduleTensor.compose A E D D P R)) h) ≪≫
            BimoduleTensor.rightBimoduleUnitIso A E D P).hom) =
      BimoduleTensor.composeMap A E D (RightModule A D)
        (𝟙 (BimoduleCategory.of A E D P)) (dgDiagonalTensorUnitIso A D Q h).hom := by
  subst Q
  simp only [eqToIso_refl, Iso.refl_trans, dgDiagonalTensorUnitIso]
  change (BimoduleTensor.associatorIso A E D D (RightModule A D)
      P (Bimodule.diagonal A D) (DGFunctor.id _)).inv ≫
      BimoduleTensor.composeMap A E D (RightModule A D)
        (BimoduleTensor.rightBimoduleUnitIso A E D P).hom
        (𝟙 (BimoduleCategory.of A D (RightModule A D) (DGFunctor.id _))) = _
  apply (cancel_epi (BimoduleTensor.associatorIso A E D D (RightModule A D)
    P (Bimodule.diagonal A D) (DGFunctor.id _)).hom).1
  rw [Iso.hom_inv_id_assoc]
  exact BimoduleTensor.triangle A E D (RightModule A D) P (DGFunctor.id _)

/-- 同じ元の実 graph 合成比較と恒等延長の単位比較が満たす三角。 -/
lemma dgModuleExtensionCompositionTensorIso_id (F : DGFunctor A D E) :
    (dgModuleExtensionCompositionTensorIso A D D E (DGFunctor.id D) F).hom ≫
        (dgModuleGraphTensorFunctor A D E).map
          (dgFunctorGraphInputIso A D E (strictDGFunctor_id_comp F)).hom =
      BimoduleTensor.composeMap A E D (RightModule A D)
        (𝟙 (BimoduleCategory.of A E D (functorGraph A D E F)))
        (dgModuleExtensionIdentityTensorIso A D).hom := by
  simp only [dgModuleExtensionCompositionTensorIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp]
  have h := congrArg (fun e => (dgModuleGraphTensorFunctor A D E).map e.hom)
    (dgFunctorGraphCompositionIso_id A D E F)
  simp only [Iso.trans_hom] at h
  rw [h]
  exact dgDiagonalTensorUnit_triangle A D E (functorGraph A D E F) _
    (functorGraph_identity A D)

end SerrePositivity.KST.SConstruction
