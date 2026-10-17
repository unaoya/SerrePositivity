module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionNaturalIso

/-! # 主導来kernelの作用の合成比較

## 概要
両kernelが指定bimodule局所化の任意対象であるとき、作用の合成を導来合成kernelの作用へ比較する。

## 方針
K-flat代表上の自然な作用比較を、指定準同型の積局所化から全kernelへ延長する。

## 規約と注意
kernelはD→Eについて右E・左D。必要な局所Hom条件は始域Dだけ。
入力導来加群と全導来kernel射に自然。単位・結合coherenceは別途検証する。

## 使われ方
U16aの公開kernelCompositionIsoと、U16dのPerf合成比較の具体的入力を提供する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]

/-- K-flat代表と通常代表について、導来合成kernelの作用を実際の通常合成作用へ比較する。 -/
def kernelCompositionKFlatIso (hD : localHomKFlat A D)
    (P : RightKFlatBimoduleCategory A E D) (Q : BimoduleCategory A F E) :
    kernelDerivedTensor A D E ((bimoduleToDerived A E D).obj P.obj) ⋙
        kernelDerivedTensor A E F ((bimoduleToDerived A F E).obj Q) ≅
      kernelDerivedTensor A D F
        (kernelCompose A D E F hD ((bimoduleToDerived A E D).obj P.obj)
          ((bimoduleToDerived A F E).obj Q)) :=
  Functor.isoWhiskerRight (kernelDerivedTensorOnBimoduleIso A D E P.obj)
      (kernelDerivedTensor A E F ((bimoduleToDerived A F E).obj Q)) ≪≫
    Functor.isoWhiskerLeft
      (kernelDerivedTensorOnBimodule A D E (BimoduleCategory.underlying A E D P.obj))
      (kernelDerivedTensorOnBimoduleIso A E F Q) ≪≫
    kernelDerivedTensorOnBimoduleCompositionIso A D E F
      (BimoduleCategory.underlying A E D P.obj) (BimoduleCategory.underlying A F E Q)
      P.property ≪≫
    (kernelDerivedTensorOnBimoduleIso A D F (BimoduleCategory.of A F D
      (BimoduleTensor.compose A F E D (BimoduleCategory.underlying A F E Q)
        (BimoduleCategory.underlying A E D P.obj)))).symm ≪≫
    (kernelDerivedTensorFunctor A D F).mapIso
      (derivedBimoduleComposeKFlatValueIso A F E D hD P Q).symm

/-- 任意の主導来kernelの作用の合成比較。必要な局所Hom条件はDだけ。 -/
def kernelCompositionIso (hD : localHomKFlat A D)
    (P : Kernel A D E) (Q : Kernel A E F) :
    kernelDerivedTensor A D E P ⋙ kernelDerivedTensor A E F Q ≅
      kernelDerivedTensor A D F (kernelCompose A D E F hD P Q) :=
  (kernelCompositionNaturalIso A D E F hD).app (P, Q)

/-- 公開した作用合成比較は、両kernelの任意の主導来射に自然。 -/
lemma kernelCompositionIso_naturality (hD : localHomKFlat A D)
    {P P' : Kernel A D E} {Q Q' : Kernel A E F} (f : P ⟶ P') (g : Q ⟶ Q') :
    NatTrans.hcomp ((kernelDerivedTensorFunctor A D E).map f)
        ((kernelDerivedTensorFunctor A E F).map g) ≫
        (kernelCompositionIso A D E F hD P' Q').hom =
      (kernelCompositionIso A D E F hD P Q).hom ≫
        (kernelDerivedTensorFunctor A D F).map (kernelComposeMap A D E F hD f g) := by
  have h := (kernelCompositionNaturalIso A D E F hD).hom.naturality
    (show (P, Q) ⟶ (P', Q') from (f, g))
  simp only [kernelActionCompositionBifunctor_map, kernelCompositeActionBifunctor_map] at h
  exact h

/-- 公開合成比較はK-flat代表上では、同じ指定モデルの自然な比較そのものを計算する。 -/
lemma kernelCompositionIso_model (hD : localHomKFlat A D)
    (P : RightKFlatBimoduleCategory A E D) (Q : BimoduleCategory A F E) :
    kernelCompositionIso A D E F hD ((bimoduleToDerived A E D).obj P.obj)
        ((bimoduleToDerived A F E).obj Q) =
      kernelCompositionModelIso A D E F hD P Q := by
  apply Iso.ext
  change (kernelCompositionNaturalIso A D E F hD).hom.app
    ((kernelCompositionModels A D E F).obj (P, Q)) = _
  simp only [kernelCompositionNaturalIso, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app]
  change 𝟙 _ ≫ (kernelCompositionModelNatIso A D E F hD).hom.app (P, Q) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]
  rfl

/-- 自然なモデル比較は、既存のK-flat代表上の合成比較と一致する。 -/
lemma kernelCompositionModelIso_eq_kFlat (hD : localHomKFlat A D)
    (P : RightKFlatBimoduleCategory A E D) (Q : BimoduleCategory A F E) :
    kernelCompositionModelIso A D E F hD P Q = kernelCompositionKFlatIso A D E F hD P Q := by
  apply Iso.ext
  simp only [kernelCompositionModelIso, kernelCompositionKFlatIso, kernelCompositionTargetIso,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatIso.hcomp_hom,
    NatTrans.hcomp_eq_whiskerRight_comp_whiskerLeft, Category.assoc]

/-- 全導来kernelの公開比較は、K-flat代表上で既存の計算比較を保つ。 -/
lemma kernelCompositionIso_kFlat (hD : localHomKFlat A D)
    (P : RightKFlatBimoduleCategory A E D) (Q : BimoduleCategory A F E) :
    kernelCompositionIso A D E F hD ((bimoduleToDerived A E D).obj P.obj)
        ((bimoduleToDerived A F E).obj Q) = kernelCompositionKFlatIso A D E F hD P Q := by
  rw [kernelCompositionIso_model, kernelCompositionModelIso_eq_kFlat]

end SerrePositivity.DifferentialGraded.Morita
