module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceAssociatorAugmentation

/-! # 右K-flat kernelモデルでの導来作用の結合coherence

## 概要
最初の二kernelを右相対K-flatとした通常代表で、全導来入力の結合図式を証明する。

## 方針
射影入力で両経路に同じ増大を合成し、通常作用の結合図式へ帰着してから増大を消去する。

## 規約と注意
局所Hom K-flat性は不要。最後のkernelにはK-flat性を要求しない。

## 使われ方
U16aの主導来kernel全体の結合coherenceの計算モデル。
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
  (P : Bimodule A E D) (Q : Bimodule A F E) (R : Bimodule A G F)
  (hP : Bimodule.rightRelativeKFlat A E D P) (hQ : Bimodule.rightRelativeKFlat A F E Q)

/-- 相対K-flat入力での三因子導来作用の結合図式。 -/
lemma kernelDerivedTensorOnBimoduleCompositionIso_associator_app
    (M : ModuleCategory A D)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M)) :
    (kernelDerivedTensorOnBimodule A F G R).map
        ((kernelDerivedTensorOnBimoduleCompositionIso A D E F P Q hP).hom.app
          ((moduleToDerived A D).obj M)) ≫
      (kernelDerivedTensorOnBimoduleCompositionIso A D F G
        (BimoduleTensor.compose A F E D Q P) R
        (Bimodule.rightRelativeKFlat_compose A F E D Q P hQ hP)).hom.app
          ((moduleToDerived A D).obj M) =
    (kernelDerivedTensorOnBimoduleCompositionIso A E F G Q R hQ).hom.app
        ((kernelDerivedTensorOnBimodule A D E P).obj ((moduleToDerived A D).obj M)) ≫
      (kernelDerivedTensorOnBimoduleCompositionIso A D E G P
        (BimoduleTensor.compose A G F E R Q) hP).hom.app ((moduleToDerived A D).obj M) ≫
      (kernelResolutionDerivedTensorMap A D G (moduleCanonicalProjectiveResolution A D)
        (associatorIso A G F E D R Q P).hom).app ((moduleToDerived A D).obj M) := by
  let C := BimoduleTensor.compose A G F D R (BimoduleTensor.compose A F E D Q P)
  have := kernelDerivedTensorAugmentation_isIso_of_relativeKFlat A D G C M hM
  apply (cancel_mono ((kernelDerivedTensorAugmentation A D G C).app M)).1
  simp only [Category.assoc]
  rw [kernelAssociatorLeft_augmentation A D E F G P Q R hP hQ M,
    kernelAssociatorRight_augmentation A D E F G P Q R hP hQ M]
  have hc := congrArg (moduleToDerived A G).map
    (kernelTensorCompositionClosedIso_associator A D E F G P Q R M)
  simp only [Functor.map_comp] at hc
  simpa only [Category.assoc] using congrArg
    (fun k => kernelTripleAugmentation A D E F G P Q R M ≫ k) hc

/-- 指定した右K-flat二因子の導来作用の合成比較は、元の結合子と整合する。 -/
lemma kernelDerivedTensorOnBimoduleCompositionIso_associator :
    whiskerRight (kernelDerivedTensorOnBimoduleCompositionIso A D E F P Q hP).hom
        (kernelDerivedTensorOnBimodule A F G R) ≫
      (kernelDerivedTensorOnBimoduleCompositionIso A D F G
        (BimoduleTensor.compose A F E D Q P) R
        (Bimodule.rightRelativeKFlat_compose A F E D Q P hQ hP)).hom =
    (Functor.associator (kernelDerivedTensorOnBimodule A D E P)
      (kernelDerivedTensorOnBimodule A E F Q) (kernelDerivedTensorOnBimodule A F G R)).hom ≫
      whiskerLeft (kernelDerivedTensorOnBimodule A D E P)
        (kernelDerivedTensorOnBimoduleCompositionIso A E F G Q R hQ).hom ≫
      (kernelDerivedTensorOnBimoduleCompositionIso A D E G P
        (BimoduleTensor.compose A G F E R Q) hP).hom ≫
      kernelResolutionDerivedTensorMap A D G (moduleCanonicalProjectiveResolution A D)
        (associatorIso A G F E D R Q P).hom := by
  apply kernelActionNatTrans_ext_projective A D
  intro M hM
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Functor.associator_hom_app]
  erw [Category.id_comp]
  exact kernelDerivedTensorOnBimoduleCompositionIso_associator_app A D E F G P Q R hP hQ M
    (moduleHomotopicallyProjective_relativeKFlat A D hM)

end SerrePositivity.DifferentialGraded.Morita
