module
public import SerrePositivity.DifferentialGraded.Verdier.KernelComparisonNaturality
public import SerrePositivity.DifferentialGraded.Verdier.KaroubiMapShift
public import SerrePositivity.DifferentialGraded.Morita.PerfectDerivedKernelComposition

/-! # 実際の kernel 合成比較の指定商への降下

必要な局所 Hom の K-flat 条件は元の始域 D のものだけを保持する。
-/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Idempotents Morita
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (B : Type z) [DGCategory A B] [Small.{u} B]
  (S : Set D) (T : Set E) (U : Set B) (hD : localHomKFlat A D)
  (P : SupportedPerfectKernelCategory A D E S T)
  (Q : SupportedPerfectKernelCategory A E B T U)

lemma supportedKernelComposite_columns (d : D) (hd : d ∈ S) :
    modulePerfectOver A B U ((kernelDerivedColumn A D B d).obj
      (kernelCompose A D E B hD P.obj Q.obj)) := by
  let M := (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d))
  have hP : modulePerfectOver A E T ((kernelDerivedTensor A D E P.obj).obj M) :=
    (modulePerfectOver A E T).prop_of_iso (kernelDerivedColumnActionIso A D E P.obj d).symm
      (P.property.2 d hd)
  have hQ := mainKernelAction_perfectOver A E B Q.obj T U Q.property.2 hP
  exact (modulePerfectOver A B U).prop_of_iso
    ((kernelCompositionIso A D E B hD P.obj Q.obj).app M ≪≫
      kernelDerivedColumnActionIso A D B (kernelCompose A D E B hD P.obj Q.obj) d) hQ

/-- 実際の主導来合成は、指定生成集合を対応させる許容 kernel を再び与える。 -/
def supportedKernelComposite : SupportedPerfectKernelCategory A D B S U :=
  ⟨kernelCompose A D E B hD P.obj Q.obj,
    kernelCompose_columnsPerfect_of_columns A D E B hD P.obj Q.obj P.property.1 Q.property.1,
    supportedKernelComposite_columns A D E B S T U hD P Q⟩

/-- 実際の主導来合成を許容 kernel の積圏に制限する。両 kernel の全射を保持する。 -/
def supportedKernelComposeFunctor :
    SupportedPerfectKernelCategory A D E S T × SupportedPerfectKernelCategory A E B T U ⥤
      SupportedPerfectKernelCategory A D B S U :=
  (supportedPerfectKernels A D B S U).lift
    (((supportedPerfectKernels A D E S T).ι.prod (supportedPerfectKernels A E B T U).ι) ⋙
      uncurry.obj (BimoduleTensor.derivedBimoduleComposeFunctor A B E D hD))
    (fun X => (supportedKernelComposite A D E B S T U hD X.1 X.2).property)

lemma supportedKernelComposeFunctor_map
    {X Y : SupportedPerfectKernelCategory A D E S T × SupportedPerfectKernelCategory A E B T U}
    (f : X ⟶ Y) :
    ((supportedKernelComposeFunctor A D E B S T U hD).map f).hom =
      kernelComposeMap A D E B hD f.1.hom f.2.hom := rfl

/-- 合成 kernel の Perf 作用への比較は U16a・U16d の実際の公開同型。 -/
def supportedKernelPerfectCompositionIso :
    (supportedKernelPerfectFunctor A D E S T).obj P ⋙
        (supportedKernelPerfectFunctor A E B T U).obj Q ≅
      (supportedKernelPerfectFunctor A D B S U).obj
        (supportedKernelComposite A D E B S T U hD P Q) :=
  perfectKernelCompositionIso A D E B hD P.obj Q.obj P.property.1 Q.property.1

/-- 元の Perf 合成比較は、両許容 kernel の任意の主導来射に自然。 -/
lemma supportedKernelPerfectCompositionIso_naturality
    (P' : SupportedPerfectKernelCategory A D E S T)
    (Q' : SupportedPerfectKernelCategory A E B T U) (f : P ⟶ P') (g : Q ⟶ Q') :
    NatTrans.hcomp ((supportedKernelPerfectFunctor A D E S T).map f)
        ((supportedKernelPerfectFunctor A E B T U).map g) ≫
        (supportedKernelPerfectCompositionIso A D E B S T U hD P' Q').hom =
      (supportedKernelPerfectCompositionIso A D E B S T U hD P Q).hom ≫
        perfectDerivedKernelMap A D B
          (supportedKernelComposite A D E B S T U hD P Q).property.1
          (supportedKernelComposite A D E B S T U hD P' Q').property.1
          (kernelComposeMap A D E B hD f.hom g.hom) :=
  perfectKernelCompositionIso_kernel_naturality A D E B hD P.obj Q.obj
    P.property.1 Q.property.1 P'.obj Q'.obj P'.property.1 Q'.property.1 f.hom g.hom

/-- 二つの実際の誘導商関手の合成に対する、元の Perf 上の因子化。 -/
def supportedKernelVerdierCompositeFactors :
    perfectVerdierQuotient A D S ⋙
        ((supportedKernelVerdierFunctor A D E S T).obj P ⋙
          (supportedKernelVerdierFunctor A E B T U).obj Q) ≅
      ((supportedKernelPerfectFunctor A D E S T).obj P ⋙
        (supportedKernelPerfectFunctor A E B T U).obj Q) ⋙ perfectVerdierQuotient A B U :=
  (associator _ _ _).symm ≪≫
    isoWhiskerRight (perfectKernelVerdierSquare A D E P.obj P.property.1 S T P.property.2) _ ≪≫
    associator _ _ _ ≪≫
    isoWhiskerLeft _ (perfectKernelVerdierSquare A E B Q.obj Q.property.1 T U Q.property.2) ≪≫
    (associator _ _ _).symm

local instance supportedKernelVerdierCompositeLifting :
    Localization.Lifting (perfectVerdierQuotient A D S) (perfectNullObjects A D S).trW
      (((supportedKernelPerfectFunctor A D E S T).obj P ⋙
        (supportedKernelPerfectFunctor A E B T U).obj Q) ⋙ perfectVerdierQuotient A B U)
      ((supportedKernelVerdierFunctor A D E S T).obj P ⋙
        (supportedKernelVerdierFunctor A E B T U).obj Q) :=
  ⟨supportedKernelVerdierCompositeFactors A D E B S T U P Q⟩

local instance supportedKernelCompositionTargetLifting :
    Localization.Lifting (perfectVerdierQuotient A D S) (perfectNullObjects A D S).trW
      ((supportedKernelPerfectFunctor A D B S U).obj
        (supportedKernelComposite A D E B S T U hD P Q) ⋙ perfectVerdierQuotient A B U)
      ((supportedKernelVerdierFunctor A D B S U).obj
        (supportedKernelComposite A D E B S T U hD P Q)) :=
  ⟨perfectKernelVerdierSquare A D B (supportedKernelComposite A D E B S T U hD P Q).obj
    (supportedKernelComposite A D E B S T U hD P Q).property.1 S U
    (supportedKernelComposite A D E B S T U hD P Q).property.2⟩

/-- 元の作用の合成比較を先に局所化して得る、実際の商関手の合成同型。 -/
def supportedKernelVerdierCompositionIso :
    (supportedKernelVerdierFunctor A D E S T).obj P ⋙
        (supportedKernelVerdierFunctor A E B T U).obj Q ≅
      (supportedKernelVerdierFunctor A D B S U).obj
        (supportedKernelComposite A D E B S T U hD P Q) :=
  Localization.liftNatIso (perfectVerdierQuotient A D S) (perfectNullObjects A D S).trW
    _ _ _ _ (isoWhiskerRight
      (supportedKernelPerfectCompositionIso A D E B S T U hD P Q) (perfectVerdierQuotient A B U))

/-- 元の Perf 対象上で、合成比較の降下は元の比較そのものを計算する。 -/
lemma supportedKernelVerdierCompositionIso_app (X : PerfectModuleCategory A D) :
    (supportedKernelVerdierCompositionIso A D E B S T U hD P Q).hom.app
        ((perfectVerdierQuotient A D S).obj X) =
      (supportedKernelVerdierCompositeFactors A D E B S T U P Q).hom.app X ≫
        (perfectVerdierQuotient A B U).map
          ((supportedKernelPerfectCompositionIso A D E B S T U hD P Q).hom.app X) ≫
        (perfectKernelVerdierSquare A D B
          (supportedKernelComposite A D E B S T U hD P Q).obj
          (supportedKernelComposite A D E B S T U hD P Q).property.1 S U
          (supportedKernelComposite A D E B S T U hD P Q).property.2).inv.app X :=
  Localization.liftNatTrans_app _ _ _ _ _ _ _ X

/-- 実際の Karoubi 延長の合成比較に、指定商上の kernel 合成同型を適用する。 -/
def supportedKernelCompletedCompositionIso :
    (supportedKernelCompletedFunctor A D E S T).obj P ⋙
        (supportedKernelCompletedFunctor A E B T U).obj Q ≅
      (supportedKernelCompletedFunctor A D B S U).obj
        (supportedKernelComposite A D E B S T U hD P Q) :=
  karoubiFunctorCompositionIso _ _ ≪≫
    (functorExtension₂ _ _).mapIso (supportedKernelVerdierCompositionIso A D E B S T U hD P Q)
end SerrePositivity.DifferentialGraded
