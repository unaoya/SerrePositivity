module
public import SerrePositivity.DifferentialGraded.Morita.U16a
public import SerrePositivity.DifferentialGraded.Morita.PerfectDerivedKernelComposition

/-! # 実際のPerf作用比較の両単位coherence

## 概要
受入済みの主導来作用の両単位図式を、別担当の既存Perf作用比較そのものへ移す。

## 方針
Perf包含の忠実性と既存制限の成分式を使い、元の公開図式に帰着する。

## 規約と注意
公開比較の定義を変更しない。必要な局所Hom条件と列のperfect性は保持する。

## 使われ方
U16dの既存Perf比較にU16aの作用coherenceを供給するアダプタ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (hD : localHomKFlat A D)
  (P : Kernel A D E) (hP : kernelColumnsPerfect A D E P)

/-- 既存の実際のPerf合成比較と右単位子は整合する。 -/
lemma perfectKernelCompositionIso_rightUnit :
    (perfectKernelCompositionIso A D D E hD (kernelIdentity A D) P
      (kernelIdentity_columnsPerfect A D) hP).hom ≫
      perfectDerivedKernelMap A D E
        (kernelCompose_columnsPerfect_of_columns A D D E hD (kernelIdentity A D) P
          (kernelIdentity_columnsPerfect A D) hP) hP
        ((derivedBimoduleRightUnitIso A E D hD).hom.app P) =
    whiskerRight (perfectDerivedKernelIdentityIso A D).hom (perfectDerivedKernelAction A D E P hP) ≫
      (Functor.leftUnitor (perfectDerivedKernelAction A D E P hP)).hom := by
  apply NatTrans.ext
  funext X
  apply (modulePerfect A E).hom_ext
  have h := NatTrans.congr_app (kernelCompositionIso_rightUnit A D E hD P) X.obj
  simp only [NatTrans.comp_app, whiskerRight_app, Functor.leftUnitor_hom_app] at h
  simp only [NatTrans.comp_app, whiskerRight_app, Functor.leftUnitor_hom_app,
    perfectKernelCompositionIso, perfectDerivedKernelCompositionIso, perfectFunctorCompositionIso,
    perfectFunctorIso, perfectDerivedKernelIdentityIso, perfectFunctorIdentityIso,
    Iso.trans_hom, NatIso.ofComponents, ObjectProperty.isoMk, Iso.refl_hom, NatTrans.id_app]
  change (𝟙 _ ≫ (kernelCompositionIso A D D E hD (kernelIdentity A D) P).hom.app X.obj) ≫
      ((kernelDerivedTensorFunctor A D E).map
        ((derivedBimoduleRightUnitIso A E D hD).hom.app P)).app X.obj =
    (kernelDerivedTensor A D E P).map ((kernelIdentityIso A D).hom.app X.obj ≫ 𝟙 _) ≫ 𝟙 _
  erw [Category.comp_id] at h
  simpa only [Category.id_comp, Category.comp_id] using h

/-- 既存の実際のPerf合成比較と左単位子は整合する。 -/
lemma perfectKernelCompositionIso_leftUnit (hE : localHomKFlat A E) :
    (perfectKernelCompositionIso A D E E hD P (kernelIdentity A E)
      hP (kernelIdentity_columnsPerfect A E)).hom ≫
      perfectDerivedKernelMap A D E
        (kernelCompose_columnsPerfect_of_columns A D E E hD P (kernelIdentity A E)
          hP (kernelIdentity_columnsPerfect A E)) hP
        ((derivedBimoduleLeftUnitIso A E D hD).hom.app P) =
    whiskerLeft (perfectDerivedKernelAction A D E P hP) (perfectDerivedKernelIdentityIso A E).hom ≫
      (Functor.rightUnitor (perfectDerivedKernelAction A D E P hP)).hom := by
  apply NatTrans.ext
  funext X
  apply (modulePerfect A E).hom_ext
  have h := NatTrans.congr_app (kernelCompositionIso_leftUnit A D E hD hE P) X.obj
  simp only [NatTrans.comp_app, whiskerLeft_app, Functor.rightUnitor_hom_app] at h
  simp only [NatTrans.comp_app, whiskerLeft_app, Functor.rightUnitor_hom_app,
    perfectKernelCompositionIso, perfectDerivedKernelCompositionIso, perfectFunctorCompositionIso,
    perfectFunctorIso, perfectDerivedKernelIdentityIso, perfectFunctorIdentityIso,
    Iso.trans_hom, NatIso.ofComponents, ObjectProperty.isoMk, Iso.refl_hom, NatTrans.id_app]
  change (𝟙 _ ≫ (kernelCompositionIso A D E E hD P (kernelIdentity A E)).hom.app X.obj) ≫
      ((kernelDerivedTensorFunctor A D E).map
        ((derivedBimoduleLeftUnitIso A E D hD).hom.app P)).app X.obj =
    ((kernelIdentityIso A E).hom.app ((kernelDerivedTensor A D E P).obj X.obj) ≫ 𝟙 _) ≫ 𝟙 _
  erw [Category.comp_id] at h
  simpa only [Category.id_comp, Category.comp_id] using h

end SerrePositivity.DifferentialGraded.Morita
