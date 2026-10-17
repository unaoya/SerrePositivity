module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionKFlatNaturality

/-! # 導来作用合成と通常tensor増大の互換性

## 概要
主導来作用の合成比較を、解像度の増大を通して通常のtensor結合比較へ接続する。

## 方針
同じ標準解像度の計算同型を消去し、増大と通常結合比較の入力自然性を使う。

## 規約と注意
最初のkernelの右相対K-flat性を明示し、局所Hom K-flat性は要求しない。

## 使われ方
U16aの単位・結合の作用coherenceを通常のbimoduleのcoherenceに帰着する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- 自然な解像度モデルの成分は指定解像度の計算同型そのもの。 -/
lemma kernelResolutionTensorModelIso_hom_app (P : Bimodule A E D)
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (M : ModuleCategory A D) :
    (kernelResolutionTensorModelIso A D E P R).hom.app M =
      (kernelResolutionDerivedTensorComputation A D E P R M).hom := by
  simp only [kernelResolutionTensorModelIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, whiskerRight_app,
    kernelResolutionDerivedTensorComputation, Functor.mapIso_hom]
  erw [Category.id_comp]
  rfl

/-- 自然な標準解像度モデルと通常tensor増大の可換square。 -/
lemma kernelResolutionTensorModelIso_augmentation (P : Bimodule A E D)
    (M : ModuleCategory A D) :
    (kernelResolutionTensorModelIso A D E P
        (moduleCanonicalProjectiveResolution A D)).hom.app M ≫
      (moduleToDerived A E).map
        ((kernelTensor A D E P).onClosed.map (moduleCanonicalProjectiveResolution A D M).π) =
      (kernelDerivedTensorAugmentation A D E P).app M := by
  rw [kernelResolutionTensorModelIso_hom_app]
  exact (kernelDerivedTensorAugmentation_app A D E P M).symm

variable (F : Type z) [DGCategory A F] [Small.{u} F]

/-- 導来合成比較と増大を通る経路は、二つの増大と通常合成比較を通る経路に一致する。 -/
lemma kernelDerivedTensorOnBimoduleCompositionIso_augmentation
    (P : Bimodule A E D) (Q : Bimodule A F E)
    (hP : Bimodule.rightRelativeKFlat A E D P) (M : ModuleCategory A D) :
    (kernelDerivedTensorOnBimoduleCompositionIso A D E F P Q hP).hom.app
        ((moduleToDerived A D).obj M) ≫
      (kernelDerivedTensorAugmentation A D F (BimoduleTensor.compose A F E D Q P)).app M =
    (kernelDerivedTensorOnBimodule A E F Q).map
        ((kernelDerivedTensorAugmentation A D E P).app M) ≫
      (kernelDerivedTensorAugmentation A E F Q).app ((kernelTensor A D E P).onClosed.obj M) ≫
        (moduleToDerived A F).map ((kernelTensorCompositionClosedIso A D E F P Q).hom.app M) := by
  let R := moduleCanonicalProjectiveResolution A D
  let C := BimoduleTensor.compose A F E D Q P
  let π := (R M).π
  let eP := (kernelResolutionTensorModelIso A D E P R).app M
  let eC := (kernelResolutionTensorModelIso A D F C R).app M
  have hC : eC.inv ≫ (kernelDerivedTensorAugmentation A D F C).app M =
      (moduleToDerived A F).map ((kernelTensor A D F C).onClosed.map π) := by
    rw [← kernelResolutionTensorModelIso_augmentation A D F C M]
    exact eC.inv_hom_id_assoc _
  have hN := (kernelTensorCompositionClosedIso A D E F P Q).hom.naturality π
  simp only [Functor.comp_map] at hN
  have hNc := congrArg (moduleToDerived A F).map hN
  simp only [Functor.map_comp] at hNc
  have hA := (kernelDerivedTensorAugmentation A E F Q).naturality
    ((kernelTensor A D E P).onClosed.map π)
  simp only [Functor.comp_map] at hA
  rw [kernelDerivedTensorOnBimoduleCompositionIso_hom_app,
    kernelResolutionTensorCompositionIso_hom_app]
  change (((kernelDerivedTensorOnBimodule A E F Q).map eP.hom ≫
    (kernelDerivedTensorAugmentation A E F Q).app ((kernelTensor A D E P).onClosed.obj (R M).obj) ≫
    (moduleToDerived A F).map ((kernelTensorCompositionClosedIso A D E F P Q).hom.app (R M).obj)) ≫
    eC.inv) ≫ _ = _
  rw [Category.assoc, hC]
  simp only [Category.assoc]
  slice_lhs 3 4 => rw [← hNc]
  slice_lhs 2 3 => erw [← hA]
  simp only [Category.assoc]
  slice_lhs 1 2 => rw [← Functor.map_comp]
  have hPaug := kernelResolutionTensorModelIso_augmentation A D E P M
  change eP.hom ≫ (moduleToDerived A E).map ((kernelTensor A D E P).onClosed.map π) = _ at hPaug
  rw [hPaug, Category.assoc]

/-- 相対K-flat入力では、導来合成比較は通常合成の同じ計算図式を与える。 -/
lemma kernelDerivedTensorOnBimoduleCompositionIso_relativeKFlat
    (P : Bimodule A E D) (Q : Bimodule A F E)
    (hP : Bimodule.rightRelativeKFlat A E D P) (M : ModuleCategory A D)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M)) :
    (kernelDerivedTensorOnBimoduleCompositionIso A D E F P Q hP).app
        ((moduleToDerived A D).obj M) ≪≫
      kernelRelativeKFlatComputation A D F (BimoduleTensor.compose A F E D Q P) M hM =
    (kernelDerivedTensorOnBimodule A E F Q).mapIso (kernelRelativeKFlatComputation A D E P M hM) ≪≫
      kernelRelativeKFlatComputation A E F Q ((kernelTensor A D E P).onClosed.obj M)
        (kernelTensor_relativeKFlat A D E P hP M hM) ≪≫
      (moduleToDerived A F).mapIso ((kernelTensorCompositionClosedIso A D E F P Q).app M) := by
  apply Iso.ext
  exact kernelDerivedTensorOnBimoduleCompositionIso_augmentation A D E F P Q hP M

end SerrePositivity.DifferentialGraded.Morita
