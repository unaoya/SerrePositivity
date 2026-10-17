module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionDerivedNaturality
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionLocalization
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionValueNaturality
public import SerrePositivity.DifferentialGraded.Morita.KernelComparisonNaturality

/-! # 全導来kernel射に自然な作用合成の同型

## 概要
二つの主導来kernelの作用合成を、導来合成kernelの作用へ自然な族として比較する。

## 方針
K-flat代表上の三つの自然な比較を合成し、指定準同型の積局所化から自然同型を延長する。

## 規約と注意
任意可換環・非有界。必要な局所Hom条件は始域Dだけ。分解変更の一般経路は経由しない。

## 使われ方
U16aの公開kernelCompositionIsoを全kernel射に自然な同型として実装し、U16dのhNatを供給する。
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

/-- モデル上の導来合成kernelの作用を、通常合成kernelの作用へ計算する同型。 -/
def kernelCompositionTargetIso (hD : localHomKFlat A D)
    (P : RightKFlatBimoduleCategory A E D) (Q : BimoduleCategory A F E) :
    kernelDerivedTensor A D F (kernelCompose A D E F hD
        ((bimoduleToDerived A E D).obj P.obj) ((bimoduleToDerived A F E).obj Q)) ≅
      kernelDerivedTensorOnBimodule A D F
        (BimoduleTensor.compose A F E D (BimoduleCategory.underlying A F E Q)
          (BimoduleCategory.underlying A E D P.obj)) :=
  (kernelDerivedTensorFunctor A D F).mapIso
      (derivedBimoduleComposeKFlatValueIso A F E D hD P Q) ≪≫
    kernelDerivedTensorOnBimoduleIso A D F (BimoduleCategory.of A F D
      (BimoduleTensor.compose A F E D (BimoduleCategory.underlying A F E Q)
        (BimoduleCategory.underlying A E D P.obj)))

/-- 導来合成kernelのモデル計算は、両kernel射に自然。 -/
lemma kernelCompositionTargetIso_naturality (hD : localHomKFlat A D)
    {P P' : RightKFlatBimoduleCategory A E D} {Q Q' : BimoduleCategory A F E}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    (kernelDerivedTensorFunctor A D F).map
        (kernelComposeMap A D E F hD ((bimoduleToDerived A E D).map f.hom)
          ((bimoduleToDerived A F E).map g)) ≫
        (kernelCompositionTargetIso A D E F hD P' Q').hom =
      (kernelCompositionTargetIso A D E F hD P Q).hom ≫
        kernelResolutionDerivedTensorMap A D F (moduleCanonicalProjectiveResolution A D)
          (composeMap A F E D g f.hom) := by
  have hv := congrArg (kernelDerivedTensorFunctor A D F).map
    (kernelComposeKFlatValueIso_naturality A D E F hD f g)
  simp only [Functor.map_comp] at hv
  have he := kernelDerivedTensorOnBimoduleIso_naturality A D F (composeMap A F E D g f.hom)
  dsimp only [kernelCompositionTargetIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, hv, Category.assoc, he, ← Category.assoc]

/-- K-flat代表と通常代表の上の、自然な三つの比較を合成した作用合成同型。 -/
def kernelCompositionModelIso (hD : localHomKFlat A D)
    (P : RightKFlatBimoduleCategory A E D) (Q : BimoduleCategory A F E) :
    kernelDerivedTensor A D E ((bimoduleToDerived A E D).obj P.obj) ⋙
        kernelDerivedTensor A E F ((bimoduleToDerived A F E).obj Q) ≅
      kernelDerivedTensor A D F (kernelCompose A D E F hD
        ((bimoduleToDerived A E D).obj P.obj) ((bimoduleToDerived A F E).obj Q)) :=
  NatIso.hcomp (kernelDerivedTensorOnBimoduleIso A D E P.obj)
      (kernelDerivedTensorOnBimoduleIso A E F Q) ≪≫
    kernelDerivedTensorOnBimoduleCompositionIso A D E F
      (BimoduleCategory.underlying A E D P.obj) (BimoduleCategory.underlying A F E Q)
      P.property ≪≫
    (kernelCompositionTargetIso A D E F hD P Q).symm

/-- K-flatモデル上の作用合成同型は、両kernelの任意の射に自然。 -/
lemma kernelCompositionModelIso_naturality (hD : localHomKFlat A D)
    {P P' : RightKFlatBimoduleCategory A E D} {Q Q' : BimoduleCategory A F E}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    NatTrans.hcomp
        ((kernelDerivedTensorFunctor A D E).map ((bimoduleToDerived A E D).map f.hom))
        ((kernelDerivedTensorFunctor A E F).map ((bimoduleToDerived A F E).map g)) ≫
        (kernelCompositionModelIso A D E F hD P' Q').hom =
      (kernelCompositionModelIso A D E F hD P Q).hom ≫
        (kernelDerivedTensorFunctor A D F).map
          (kernelComposeMap A D E F hD ((bimoduleToDerived A E D).map f.hom)
            ((bimoduleToDerived A F E).map g)) := by
  have hs := kernelDerivedTensorOnBimoduleIso_hcomp_naturality A D E F f.hom g
  have hm := kernelDerivedTensorOnBimoduleCompositionIso_kernel_naturality A D E F
    f.hom g P.property P'.property
  have ht := kernelCompositionTargetIso_naturality A D E F hD f g
  dsimp only [kernelCompositionModelIso, Iso.trans_hom, Iso.symm_hom]
  apply (cancel_mono (kernelCompositionTargetIso A D E F hD P' Q').hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  slice_rhs 4 5 => rw [ht]
  slice_rhs 3 4 => rw [Iso.inv_hom_id]
  slice_lhs 1 2 => rw [hs]
  slice_lhs 2 3 => rw [hm]
  simp only [Category.id_comp]

/-- 指定モデルの積圏上で作用合成比較を自然同型へ束ねる。 -/
def kernelCompositionModelNatIso (hD : localHomKFlat A D) :
    kernelCompositionModels A D E F ⋙ kernelActionCompositionBifunctor A D E F ≅
      kernelCompositionModels A D E F ⋙ kernelCompositeActionBifunctor A D E F hD :=
  NatIso.ofComponents (fun X => kernelCompositionModelIso A D E F hD X.1 X.2) (by
    intro X Y f
    simp only [Functor.comp_map, kernelActionCompositionBifunctor_map,
      kernelCompositeActionBifunctor_map]
    exact kernelCompositionModelIso_naturality A D E F hD f.1 f.2)

/-- 全主導来kernelの積圏上の、任意のkernel射に自然な作用合成同型。 -/
def kernelCompositionNaturalIso (hD : localHomKFlat A D) :
    kernelActionCompositionBifunctor A D E F ≅ kernelCompositeActionBifunctor A D E F hD := by
  let := kernelCompositionModels_isLocalization A D E F hD
  exact Localization.liftNatIso (kernelCompositionModels A D E F)
    (kernelCompositionModelQuasiIso A D E F)
    (kernelCompositionModels A D E F ⋙ kernelActionCompositionBifunctor A D E F)
    (kernelCompositionModels A D E F ⋙ kernelCompositeActionBifunctor A D E F hD)
    (kernelActionCompositionBifunctor A D E F) (kernelCompositeActionBifunctor A D E F hD)
    (kernelCompositionModelNatIso A D E F hD)

end SerrePositivity.DifferentialGraded.Morita
