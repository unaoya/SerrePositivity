module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceAssociatorKFlat
public import SerrePositivity.DifferentialGraded.Morita.CoherenceComposition
public import SerrePositivity.DifferentialGraded.Morita.KernelComparisonComponents

/-! # 主導来kernel結合子と二つの右K-flat計算モデル

## 概要
公開主導来合成の結合子と、二つの通常三因子モデルを同じ計算同型で結ぶ。

## 方針
既存の全導来結合子のK-flat計算squareを評価し、kernelの向きへ読み替える。

## 規約と注意
合成の始域Dと次の圏Eの局所Hom K-flat性を明示。最後のkernelは任意。

## 使われ方
U16aの主導来kernel全体での作用結合coherenceへの移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]
  (G : Type t) [DGCategory A G] [Small.{u} G]

/-- kernelの作用順に読んだ、既存U12e-localの主導来結合子。 -/
def kernelAssociatorIso (hD : localHomKFlat A D) (hE : localHomKFlat A E)
    (P : Kernel A D E) (Q : Kernel A E F) (R : Kernel A F G) :
    kernelCompose A D E G hD P (kernelCompose A E F G hE Q R) ≅
      kernelCompose A D F G hD (kernelCompose A D E F hD P Q) R :=
  (derivedBimoduleAssociator A G F E D hE hD Q P).app R

variable (hD : localHomKFlat A D) (hE : localHomKFlat A E)
  (P : RightKFlatBimoduleCategory A E D) (Q : RightKFlatBimoduleCategory A F E)
  (R : BimoduleCategory A G F)

/-- 後二作用の合成を先に計算する三因子kernelの通常モデル。 -/
def kernelAssociatorPairModelIso :
    kernelCompose A D E G hD ((bimoduleToDerived A E D).obj P.obj)
      (kernelCompose A E F G hE ((bimoduleToDerived A F E).obj Q.obj)
        ((bimoduleToDerived A G F).obj R)) ≅
    (bimoduleToDerived A G D).obj (BimoduleCategory.of A G D
      (BimoduleTensor.compose A G E D
        (BimoduleTensor.compose A G F E (BimoduleCategory.underlying A G F R)
          (BimoduleCategory.underlying A F E Q.obj)) (BimoduleCategory.underlying A E D P.obj))) :=
  ((derivedBimoduleComposeFunctor A G E D hD).obj
      ((bimoduleToDerived A E D).obj P.obj)).mapIso
        (derivedBimoduleComposeKFlatValueIso A G F E hE Q R) ≪≫
    derivedBimoduleComposeKFlatValueIso A G E D hD P (BimoduleCategory.of A G E
      (BimoduleTensor.compose A G F E (BimoduleCategory.underlying A G F R)
        (BimoduleCategory.underlying A F E Q.obj)))

/-- 前二作用のkernelを先に計算する三因子kernelの通常モデル。 -/
def kernelAssociatorNestedModelIso :
    kernelCompose A D F G hD
      (kernelCompose A D E F hD ((bimoduleToDerived A E D).obj P.obj)
        ((bimoduleToDerived A F E).obj Q.obj)) ((bimoduleToDerived A G F).obj R) ≅
    (bimoduleToDerived A G D).obj (BimoduleCategory.of A G D
      (BimoduleTensor.compose A G F D (BimoduleCategory.underlying A G F R)
        (BimoduleTensor.compose A F E D (BimoduleCategory.underlying A F E Q.obj)
          (BimoduleCategory.underlying A E D P.obj)))) :=
  ((derivedBimoduleComposeFunctor A G F D hD).mapIso
    (derivedBimoduleComposeKFlatValueIso A F E D hD P Q.obj)).app
      ((bimoduleToDerived A G F).obj R) ≪≫
    derivedBimoduleComposeKFlatValueIso A G F D hD (rightKFlatCompose A F E D Q P) R

/-- 主導来kernel結合子の二モデル計算は、同じ通常結合子の局所化像と整合する。 -/
lemma kernelAssociatorIso_model_fac :
    (kernelAssociatorIso A D E F G hD hE
        ((bimoduleToDerived A E D).obj P.obj) ((bimoduleToDerived A F E).obj Q.obj)
        ((bimoduleToDerived A G F).obj R)).hom ≫
      (kernelAssociatorNestedModelIso A D E F G hD P Q R).hom =
    (kernelAssociatorPairModelIso A D E F G hD hE P Q R).hom ≫
      (bimoduleToDerived A G D).map (associatorIso A G F E D
        (BimoduleCategory.underlying A G F R) (BimoduleCategory.underlying A F E Q.obj)
        (BimoduleCategory.underlying A E D P.obj)).hom := by
  have h := NatTrans.congr_app
    (derivedBimoduleAssociatorIso_kFlat_fac A G F E D hE hD Q P)
      ((bimoduleToDerived A G F).obj R)
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app] at h
  rw [rightKFlatDerivedAssociator_base_app] at h
  exact h

/-- 主導来結合子の作用も、同じ通常結合子の作用のモデルsquareを満たす。 -/
lemma kernelAssociatorIso_action_model_fac :
    (kernelDerivedTensorFunctor A D G).map
        (kernelAssociatorIso A D E F G hD hE
          ((bimoduleToDerived A E D).obj P.obj) ((bimoduleToDerived A F E).obj Q.obj)
          ((bimoduleToDerived A G F).obj R)).hom ≫
      (kernelDerivedTensorFunctor A D G).map
        (kernelAssociatorNestedModelIso A D E F G hD P Q R).hom =
    (kernelDerivedTensorFunctor A D G).map
        (kernelAssociatorPairModelIso A D E F G hD hE P Q R).hom ≫
      kernelResolutionDerivedTensorMap A D G (moduleCanonicalProjectiveResolution A D)
        (associatorIso A G F E D (BimoduleCategory.underlying A G F R)
          (BimoduleCategory.underlying A F E Q.obj)
          (BimoduleCategory.underlying A E D P.obj)).hom := by
  rw [← Functor.map_comp, kernelAssociatorIso_model_fac, Functor.map_comp,
    kernelDerivedTensorFunctor_map_base]

/-- 右K-flat代表上の公開合成比較は、通常kernel作用の同じ比較を計算する。 -/
lemma kernelCompositionIso_kFlat_fac (P' : RightKFlatBimoduleCategory A E D)
    (Q' : BimoduleCategory A F E) :
    (kernelCompositionIso A D E F hD ((bimoduleToDerived A E D).obj P'.obj)
        ((bimoduleToDerived A F E).obj Q')).hom ≫
      (kernelDerivedTensorFunctor A D F).map
        (derivedBimoduleComposeKFlatValueIso A F E D hD P' Q').hom =
    (kernelDerivedTensorOnBimoduleCompositionIso A D E F
      (BimoduleCategory.underlying A E D P'.obj) (BimoduleCategory.underlying A F E Q')
      P'.property).hom := by
  rw [kernelCompositionIso_model]
  apply NatTrans.ext
  funext X
  simp only [kernelCompositionModelIso, kernelCompositionTargetIso, Iso.trans_hom,
    Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app, Functor.mapIso_inv,
    kernelDerivedTensorOnBimoduleIso_refl, Iso.refl_hom, Iso.refl_inv,
    NatIso.hcomp_hom, NatTrans.hcomp_app, NatTrans.id_app]
  erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.id_comp]
  rw [Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp, Iso.inv_hom_id]
  erw [CategoryTheory.Functor.map_id]
  rw [NatTrans.id_app]
  erw [Category.comp_id]

end SerrePositivity.DifferentialGraded.Morita
