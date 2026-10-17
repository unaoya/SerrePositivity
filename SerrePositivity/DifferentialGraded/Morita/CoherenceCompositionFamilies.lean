module
public import SerrePositivity.DifferentialGraded.Morita.KernelDerivedFunctor

/-! # 主導来kernelの作用合成を表す二つの関手族

## 概要
作用を順に合成する族と、導来合成kernelを作用させる族を同じ関手圏に置く。

## 方針
MathlibのwhiskeringLeft・whiskeringRightと既存の主導来作用・bimodule合成を合成する。

## 規約と注意
kernelはD→Eで右E・左D。合成kernel側だけに始域DのlocalHomKFlatを要求する。

## 使われ方
U16aの合成比較を全ての導来kernel射に自然な関手族の同型として構成するための入口。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]

/-- 二つの主導来kernelの作用をD→E→Fの順に合成する関手族。 -/
def kernelActionCompositionFamily :
    Kernel A D E ⥤ (Kernel A E F ⥤
      (DerivedModuleCategory A D ⥤ DerivedModuleCategory A F)) :=
  kernelDerivedTensorFunctor A D E ⋙
    whiskeringLeft (DerivedModuleCategory A D) (DerivedModuleCategory A E)
      (DerivedModuleCategory A F) ⋙
    (whiskeringLeft (Kernel A E F)
      (DerivedModuleCategory A E ⥤ DerivedModuleCategory A F)
      (DerivedModuleCategory A D ⥤ DerivedModuleCategory A F)).obj
      (kernelDerivedTensorFunctor A E F)

/-- 導来合成kernelの主導来作用を同じ二変数の関手族に置く。 -/
def kernelCompositeActionFamily (hD : localHomKFlat A D) :
    Kernel A D E ⥤ (Kernel A E F ⥤
      (DerivedModuleCategory A D ⥤ DerivedModuleCategory A F)) :=
  BimoduleTensor.derivedBimoduleComposeFunctor A F E D hD ⋙
    (whiskeringRight (Kernel A E F) (Kernel A D F)
      (DerivedModuleCategory A D ⥤ DerivedModuleCategory A F)).obj
      (kernelDerivedTensorFunctor A D F)

/-- 作用合成族の両kernel射に関する成分は、実際の二つの作用射の水平合成。 -/
lemma kernelActionCompositionFamily_map_app
    {P P' : Kernel A D E} {Q Q' : Kernel A E F} (f : P ⟶ P') (g : Q ⟶ Q') :
    ((kernelActionCompositionFamily A D E F).map f).app Q ≫
        ((kernelActionCompositionFamily A D E F).obj P').map g =
      NatTrans.hcomp ((kernelDerivedTensorFunctor A D E).map f)
        ((kernelDerivedTensorFunctor A E F).map g) := by
  apply NatTrans.ext
  funext X
  simp only [NatTrans.hcomp_app]
  change (kernelDerivedTensor A E F Q).map
      (((kernelDerivedTensorFunctor A D E).map f).app X) ≫
    ((kernelDerivedTensorFunctor A E F).map g).app ((kernelDerivedTensor A D E P').obj X) = _
  exact ((kernelDerivedTensorFunctor A E F).map g).naturality
    (((kernelDerivedTensorFunctor A D E).map f).app X)

/-- 合成kernel作用族の両kernel射に関する成分はkernelComposeMapの作用。 -/
lemma kernelCompositeActionFamily_map_app (hD : localHomKFlat A D)
    {P P' : Kernel A D E} {Q Q' : Kernel A E F} (f : P ⟶ P') (g : Q ⟶ Q') :
    ((kernelCompositeActionFamily A D E F hD).map f).app Q ≫
        ((kernelCompositeActionFamily A D E F hD).obj P').map g =
      (kernelDerivedTensorFunctor A D F).map (kernelComposeMap A D E F hD f g) :=
  ((kernelDerivedTensorFunctor A D F).map_comp _ _).symm

end SerrePositivity.DifferentialGraded.Morita
