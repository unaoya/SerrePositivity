module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceAssociator
public import SerrePositivity.DifferentialGraded.Morita.Perfect
public import Mathlib.Data.ZMod.Basic

/-! # 全導来kernel射に自然な合成比較と実際のPerf自然性の接続監査

## 概要
任意の主導来kernel射に対する作用合成の自然性と、U16dの既存hNat入力への接続を確認する。

## 方針
任意可換環・独立宇宙・標数2、既存Perfアダプタへの実際の適用と全追加公開宣言の監査を行う。

## 規約と注意
必要な局所Hom条件はDだけ。一般右随伴と作用の単位・結合coherenceは別の残課題。

## 使われ方
U16aからU16dへ、明示仮定だったhNatを証明済みAPIで渡す再現入口。
-/
@[expose] public section
noncomputable section
universe u v w z
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.Morita
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]

example (hD : localHomKFlat A D) {P P' : Kernel A D E} {Q Q' : Kernel A E F}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    NatTrans.hcomp ((kernelDerivedTensorFunctor A D E).map f)
        ((kernelDerivedTensorFunctor A E F).map g) ≫
        (kernelCompositionIso A D E F hD P' Q').hom =
      (kernelCompositionIso A D E F hD P Q).hom ≫
        (kernelDerivedTensorFunctor A D F).map (kernelComposeMap A D E F hD f g) :=
  kernelCompositionIso_naturality A D E F hD f g

example (hD : localHomKFlat A D) (P P' : Kernel A D E) (Q Q' : Kernel A E F)
    (hP : kernelColumnsPerfect A D E P) (hP' : kernelColumnsPerfect A D E P')
    (hQ : kernelColumnsPerfect A E F Q) (hQ' : kernelColumnsPerfect A E F Q')
    (f : P ⟶ P') (g : Q ⟶ Q') :
    NatTrans.hcomp (perfectDerivedKernelMap A D E hP hP' f)
        (perfectDerivedKernelMap A E F hQ hQ' g) ≫
        (perfectDerivedKernelCompositionIso A D E F hD P' Q' hP' hQ'
          (kernelCompositionIso A D E F hD P' Q')).hom =
      (perfectDerivedKernelCompositionIso A D E F hD P Q hP hQ
          (kernelCompositionIso A D E F hD P Q)).hom ≫
        perfectDerivedKernelMap A D F
          (kernelCompose_columnsPerfect A D E F hD P Q hP hQ
            (kernelCompositionIso A D E F hD P Q))
          (kernelCompose_columnsPerfect A D E F hD P' Q' hP' hQ'
            (kernelCompositionIso A D E F hD P' Q'))
          (kernelComposeMap A D E F hD f g) :=
  perfectDerivedKernelCompositionIso_naturality A D E F hD P Q hP hQ
    (kernelCompositionIso A D E F hD P Q) P' Q' hP' hQ'
    (kernelCompositionIso A D E F hD P' Q') f g
    (kernelCompositionIso_naturality A D E F hD f g)

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D]
    (E : Type w) [DGCategory (ZMod 2) E] [Small.{0} E]
    (F : Type z) [DGCategory (ZMod 2) F] [Small.{0} F]
    (hD : localHomKFlat (ZMod 2) D) :
    kernelActionCompositionBifunctor (ZMod 2) D E F ≅
      kernelCompositeActionBifunctor (ZMod 2) D E F hD :=
  kernelCompositionNaturalIso (ZMod 2) D E F hD

#check kernelCompositionIso
#check kernelCompositionIso_naturality
#check kernelCompositionIso_model
#print axioms kernelCompositionSourceModelSquare
#print axioms kernelDerivedTensorOnBimoduleCompositionIso_kernel_naturality
#print axioms kernelActionCompositionFamily
#print axioms kernelCompositeActionFamily
#print axioms kernelActionCompositionFamily_map_app
#print axioms kernelCompositeActionFamily_map_app
#print axioms kernelDerivedTensorOnBimoduleIso_naturality
#print axioms kernelDerivedTensorOnBimoduleIso_hcomp_naturality
#print axioms kernelComposeKFlatValueIso_naturality
#print axioms kernelActionCompositionBifunctor
#print axioms kernelCompositeActionBifunctor
#print axioms kernelActionCompositionBifunctor_map
#print axioms kernelCompositeActionBifunctor_map
#print axioms kernelCompositionModels
#print axioms kernelCompositionModelQuasiIso
#print axioms kernelCompositionModels_isLocalization
#print axioms kernelCompositionTargetIso
#print axioms kernelCompositionTargetIso_naturality
#print axioms kernelCompositionModelIso
#print axioms kernelCompositionModelIso_naturality
#print axioms kernelCompositionModelNatIso
#print axioms kernelCompositionNaturalIso
#print axioms kernelCompositionKFlatIso
#print axioms kernelCompositionIso
#print axioms kernelCompositionIso_naturality
#print axioms kernelCompositionIso_model
#print axioms kernelCompositionModelIso_eq_kFlat
#print axioms kernelCompositionIso_kFlat
