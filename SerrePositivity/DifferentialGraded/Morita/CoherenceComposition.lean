module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionKFlat

/-! # 主導来kernelの作用の合成比較

## 概要
両kernelが指定bimodule局所化の任意対象であるとき、作用の合成を導来合成kernelの作用へ比較する。

## 方針
最初のkernelを右相対K-flat代表に取り、通常kernelの作用比較とU12eの導来合成計算を接続する。

## 規約と注意
kernelはD→Eについて右E・左D。必要な局所Hom条件は始域Dだけ。
この同型は入力導来加群に自然。kernel射の自然性と単位・結合coherenceは別途検証する。

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
      kernelDerivedTensor A D F (kernelCompose A D E F hD P Q) := by
  let R := Classical.choose (exists_rightKFlat_derived_iso A E D hD P)
  let eP : (bimoduleToDerived A E D).obj R.obj ≅ P :=
    Classical.choice (Classical.choose_spec (exists_rightKFlat_derived_iso A E D hD P))
  let S := (bimoduleToDerived A F E).objPreimage Q
  let eQ : (bimoduleToDerived A F E).obj S ≅ Q :=
    (bimoduleToDerived A F E).objObjPreimageIso Q
  let eComp : kernelCompose A D E F hD ((bimoduleToDerived A E D).obj R.obj)
        ((bimoduleToDerived A F E).obj S) ≅ kernelCompose A D E F hD P Q :=
    ((derivedBimoduleComposeFunctor A F E D hD).mapIso eP).app
        ((bimoduleToDerived A F E).obj S) ≪≫
      ((derivedBimoduleComposeFunctor A F E D hD).obj P).mapIso eQ
  exact Functor.isoWhiskerRight ((kernelDerivedTensorFunctor A D E).mapIso eP).symm
      (kernelDerivedTensor A E F Q) ≪≫
    Functor.isoWhiskerLeft
      (kernelDerivedTensor A D E ((bimoduleToDerived A E D).obj R.obj))
      ((kernelDerivedTensorFunctor A E F).mapIso eQ).symm ≪≫
    kernelCompositionKFlatIso A D E F hD R S ≪≫
    (kernelDerivedTensorFunctor A D F).mapIso eComp

end SerrePositivity.DifferentialGraded.Morita
