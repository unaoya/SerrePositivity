module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceAssociatorClosed
public import SerrePositivity.DifferentialGraded.Morita.CoherenceProjectiveExt

/-! # 三因子の導来作用比較と共通の増大経路

## 概要
三因子作用の結合図式の二経路を、同じ三重tensor増大を通る通常図式へ接続する。

## 方針
二因子の増大squareと入力自然性を順に適用し、三つの増大を先頭にそろえる。

## 規約と注意
最初の二kernelの右相対K-flat性を明示し、局所Hom K-flat性は要求しない。

## 使われ方
U16aの通常kernelによる導来作用の結合coherence。
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

/-- 三つの通常kernel作用の導来増大を順に適用した共通経路。 -/
def kernelTripleAugmentation (M : ModuleCategory A D) :
    (kernelDerivedTensorOnBimodule A F G R).obj
      ((kernelDerivedTensorOnBimodule A E F Q).obj
        ((kernelDerivedTensorOnBimodule A D E P).obj ((moduleToDerived A D).obj M))) ⟶
    (moduleToDerived A G).obj ((kernelTensor A F G R).onClosed.obj
      ((kernelTensor A E F Q).onClosed.obj ((kernelTensor A D E P).onClosed.obj M))) :=
  (kernelDerivedTensorOnBimodule A F G R).map
      ((kernelDerivedTensorOnBimodule A E F Q).map
        ((kernelDerivedTensorAugmentation A D E P).app M)) ≫
    (kernelDerivedTensorOnBimodule A F G R).map
      ((kernelDerivedTensorAugmentation A E F Q).app ((kernelTensor A D E P).onClosed.obj M)) ≫
    (kernelDerivedTensorAugmentation A F G R).app
      ((kernelTensor A E F Q).onClosed.obj ((kernelTensor A D E P).onClosed.obj M))

/-- 前二因子を先に合成する導来経路は、共通増大と通常の同じ経路を計算する。 -/
lemma kernelAssociatorLeft_augmentation
    (hP : Bimodule.rightRelativeKFlat A E D P) (hQ : Bimodule.rightRelativeKFlat A F E Q)
    (M : ModuleCategory A D) :
    (kernelDerivedTensorOnBimodule A F G R).map
        ((kernelDerivedTensorOnBimoduleCompositionIso A D E F P Q hP).hom.app
          ((moduleToDerived A D).obj M)) ≫
      (kernelDerivedTensorOnBimoduleCompositionIso A D F G (BimoduleTensor.compose A F E D Q P) R
        (Bimodule.rightRelativeKFlat_compose A F E D Q P hQ hP)).hom.app
          ((moduleToDerived A D).obj M) ≫
      (kernelDerivedTensorAugmentation A D G
        (BimoduleTensor.compose A G F D R (BimoduleTensor.compose A F E D Q P))).app M =
    kernelTripleAugmentation A D E F G P Q R M ≫
      (moduleToDerived A G).map ((kernelTensor A F G R).onClosed.map
        ((kernelTensorCompositionClosedIso A D E F P Q).hom.app M)) ≫
      (moduleToDerived A G).map
        ((kernelTensorCompositionClosedIso A D F G
          (BimoduleTensor.compose A F E D Q P) R).hom.app M) := by
  have hn := (kernelDerivedTensorAugmentation A F G R).naturality
    ((kernelTensorCompositionClosedIso A D E F P Q).hom.app M)
  simp only [Functor.comp_map] at hn
  slice_lhs 2 3 => rw [kernelDerivedTensorOnBimoduleCompositionIso_augmentation]
  slice_lhs 1 2 => rw [← Functor.map_comp, kernelDerivedTensorOnBimoduleCompositionIso_augmentation]
  simp only [Functor.map_comp, Category.assoc]
  slice_lhs 3 4 => erw [hn]
  simp only [kernelTripleAugmentation, Category.assoc]
  rfl

/-- 後二因子を先に合成する導来経路も、同じ三重増大と通常経路を計算する。 -/
lemma kernelAssociatorRight_augmentation
    (hP : Bimodule.rightRelativeKFlat A E D P) (hQ : Bimodule.rightRelativeKFlat A F E Q)
    (M : ModuleCategory A D) :
    (kernelDerivedTensorOnBimoduleCompositionIso A E F G Q R hQ).hom.app
        ((kernelDerivedTensorOnBimodule A D E P).obj ((moduleToDerived A D).obj M)) ≫
      (kernelDerivedTensorOnBimoduleCompositionIso A D E G P
        (BimoduleTensor.compose A G F E R Q) hP).hom.app ((moduleToDerived A D).obj M) ≫
      (kernelResolutionDerivedTensorMap A D G (moduleCanonicalProjectiveResolution A D)
        (associatorIso A G F E D R Q P).hom).app ((moduleToDerived A D).obj M) ≫
      (kernelDerivedTensorAugmentation A D G
        (BimoduleTensor.compose A G F D R (BimoduleTensor.compose A F E D Q P))).app M =
    kernelTripleAugmentation A D E F G P Q R M ≫
      (moduleToDerived A G).map ((kernelTensorCompositionClosedIso A E F G Q R).hom.app
        ((kernelTensor A D E P).onClosed.obj M)) ≫
      (moduleToDerived A G).map
        ((kernelTensorCompositionClosedIso A D E G P
          (BimoduleTensor.compose A G F E R Q)).hom.app M) ≫
      (moduleToDerived A G).map
        ((kernelTensorMap A D G (associatorIso A G F E D R Q P).hom).app M) := by
  have hn := (kernelDerivedTensorOnBimoduleCompositionIso A E F G Q R hQ).hom.naturality
    ((kernelDerivedTensorAugmentation A D E P).app M)
  simp only [Functor.comp_map] at hn
  slice_lhs 3 4 => erw [kernelDerivedTensorAugmentation_kernel_naturality A D G
    (associatorIso A G F E D R Q P).hom M]
  slice_lhs 2 3 => erw [kernelDerivedTensorOnBimoduleCompositionIso_augmentation A D E G P
    (BimoduleTensor.compose A G F E R Q) hP M]
  slice_lhs 1 2 => erw [← hn]
  slice_lhs 2 3 => erw [kernelDerivedTensorOnBimoduleCompositionIso_augmentation A E F G Q R hQ
    ((kernelTensor A D E P).onClosed.obj M)]
  simp only [kernelTripleAugmentation, Category.assoc]

end SerrePositivity.DifferentialGraded.Morita
