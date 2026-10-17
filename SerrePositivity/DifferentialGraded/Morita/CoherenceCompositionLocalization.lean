module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionFamilies
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Localization.Prod

/-! # kernel作用合成の積圏表示とK-flatモデルの局所化

## 概要
二つの主導来kernelの作用合成を積圏上に置き、K-flat代表と通常代表からの積局所化を固定する。

## 方針
U12e-localのK-flat部分圏との比較同値とMathlibの積局所化を使う。

## 規約と注意
必要な局所Hom条件は始域Dだけ。モデルの射のクラスは各指定準同型の積。

## 使われ方
U16aの合成比較を全導来kernelの任意射に自然な同型へ延長する。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]

/-- 二つの作用を合成する関手を、kernelの積圏上で読む。 -/
def kernelActionCompositionBifunctor : Kernel A D E × Kernel A E F ⥤
    (DerivedModuleCategory A D ⥤ DerivedModuleCategory A F) :=
  uncurry.obj (kernelActionCompositionFamily A D E F)

/-- 導来合成kernelの作用を、同じ積圏上で読む。 -/
def kernelCompositeActionBifunctor (hD : localHomKFlat A D) :
    Kernel A D E × Kernel A E F ⥤
      (DerivedModuleCategory A D ⥤ DerivedModuleCategory A F) :=
  uncurry.obj (kernelCompositeActionFamily A D E F hD)

/-- 作用合成の積圏上のmapは、二つの作用射の水平合成。 -/
lemma kernelActionCompositionBifunctor_map
    {X Y : Kernel A D E × Kernel A E F} (f : X ⟶ Y) :
    (kernelActionCompositionBifunctor A D E F).map f =
      NatTrans.hcomp ((kernelDerivedTensorFunctor A D E).map f.1)
        ((kernelDerivedTensorFunctor A E F).map f.2) :=
  kernelActionCompositionFamily_map_app A D E F f.1 f.2

/-- 導来合成kernel作用の積圏上のmapは、kernelComposeMapの作用。 -/
lemma kernelCompositeActionBifunctor_map (hD : localHomKFlat A D)
    {X Y : Kernel A D E × Kernel A E F} (f : X ⟶ Y) :
    (kernelCompositeActionBifunctor A D E F hD).map f =
      (kernelDerivedTensorFunctor A D F).map (kernelComposeMap A D E F hD f.1 f.2) :=
  kernelCompositeActionFamily_map_app A D E F hD f.1 f.2

/-- 最初のkernelを右K-flat代表で、後のkernelを通常代表で与える積関手。 -/
def kernelCompositionModels : RightKFlatBimoduleCategory A E D × BimoduleCategory A F E ⥤
    Kernel A D E × Kernel A E F :=
  (rightKFlatInclusion A E D ⋙ bimoduleToDerived A E D).prod (bimoduleToDerived A F E)

/-- 上の積モデルで反転する射は、各既存準同型クラスの積。 -/
def kernelCompositionModelQuasiIso : MorphismProperty
    (RightKFlatBimoduleCategory A E D × BimoduleCategory A F E) :=
  (rightKFlatQuasiIso A E D).prod (BimoduleCategory.quasiIso A F E)

/-- Dの局所Hom K-flat性により、モデルの積関手は指定した準同型の積に関する局所化。 -/
lemma kernelCompositionModels_isLocalization (hD : localHomKFlat A D) :
    (kernelCompositionModels A D E F).IsLocalization (kernelCompositionModelQuasiIso A D E F) := by
  let := rightKFlatDerivedInclusion_isEquivalence A E D hD
  let : (rightKFlatQuasiIso A E D).ContainsIdentities := by
    dsimp only [rightKFlatQuasiIso]
    infer_instance
  let : (rightKFlatInclusion A E D ⋙ bimoduleToDerived A E D).IsLocalization
      (rightKFlatQuasiIso A E D) :=
    Functor.IsLocalization.of_iso (W := rightKFlatQuasiIso A E D)
      (eqToIso (rightKFlatDerivedInclusion_fac A E D))
  dsimp only [kernelCompositionModels, kernelCompositionModelQuasiIso]
  infer_instance

end SerrePositivity.DifferentialGraded.Morita
