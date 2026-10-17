module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionClosed
public import SerrePositivity.DifferentialGraded.Morita.KernelResolutionModel

/-! # 右相対K-flat kernelによる導来作用の合成

## 概要
最初のkernelの右相対K-flat性から、二つの主導来作用の合成を通常合成kernelの作用へ比較する。

## 方針
射影入力のtensorが相対K-flatになることをFubiniで示し、自然な解像度モデル上の同型を局所化から延長する。

## 規約と注意
局所Hom条件は不要。最初のkernelの右相対K-flat性を明示し、後のkernelには追加条件を課さない。

## 使われ方
U16aの全導来kernelの合成比較を、U12e-localのK-flat代表による計算へ接続する。
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
  (F : Type z) [DGCategory A F] [Small.{u} F]
  (P : Bimodule A E D) (Q : Bimodule A F E)
  (hP : Bimodule.rightRelativeKFlat A E D P)
  (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)

/-- 解像度モデル上で、後のkernelの導来作用を相対K-flat入力計算へ置き換える。 -/
def kernelResolutionTensorCompositionIso :
    kernelResolutionTensorModelFunctor A D E P R ⋙ kernelDerivedTensorOnBimodule A E F Q ≅
      kernelResolutionTensorModelFunctor A D F (BimoduleTensor.compose A F E D Q P) R :=
  NatIso.ofComponents (fun M =>
    kernelRelativeKFlatComputation A E F Q ((kernelTensor A D E P).onClosed.obj (R M).obj)
      (kernelTensor_relativeKFlat A D E P hP (R M).obj
        (moduleHomotopicallyProjective_relativeKFlat A D (R M).projective)) ≪≫
      (moduleToDerived A F).mapIso
        ((kernelTensorCompositionClosedIso A D E F P Q).app (R M).obj)) (by
    intro M N f
    simp only [Functor.comp_map, kernelResolutionTensorModelFunctor_map]
    change (kernelDerivedTensorOnBimodule A E F Q).map
        ((moduleToDerived A E).map ((kernelTensor A D E P).onClosed.map ((R M).lift (R N) f))) ≫
        ((kernelDerivedTensorAugmentation A E F Q).app _ ≫
          (moduleToDerived A F).map
            ((kernelTensorCompositionClosedIso A D E F P Q).hom.app (R N).obj)) =
      ((kernelDerivedTensorAugmentation A E F Q).app _ ≫
          (moduleToDerived A F).map
            ((kernelTensorCompositionClosedIso A D E F P Q).hom.app (R M).obj)) ≫ _
    rw [← Category.assoc]
    have hn := (kernelDerivedTensorAugmentation A E F Q).naturality
      ((kernelTensor A D E P).onClosed.map ((R M).lift (R N) f))
    simp only [Functor.comp_map] at hn
    rw [hn]
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun k => (kernelDerivedTensorAugmentation A E F Q).app _ ≫
      (moduleToDerived A F).map k)
      ((kernelTensorCompositionClosedIso A D E F P Q).hom.naturality ((R M).lift (R N) f)))

/-- 右相対K-flatな最初のkernelについて、主導来作用の合成は通常合成kernelの作用と同型。 -/
def kernelDerivedTensorOnBimoduleCompositionIso :
    kernelDerivedTensorOnBimodule A D E P ⋙ kernelDerivedTensorOnBimodule A E F Q ≅
      kernelDerivedTensorOnBimodule A D F (BimoduleTensor.compose A F E D Q P) := by
  let R := moduleCanonicalProjectiveResolution A D
  let G := kernelDerivedTensorOnBimodule A D E P ⋙ kernelDerivedTensorOnBimodule A E F Q
  let H := kernelDerivedTensorOnBimodule A D F (BimoduleTensor.compose A F E D Q P)
  let e : moduleToDerived A D ⋙ G ≅ moduleToDerived A D ⋙ H :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (kernelResolutionTensorModelIso A D E P R)
        (kernelDerivedTensorOnBimodule A E F Q) ≪≫
      kernelResolutionTensorCompositionIso A D E F P Q hP R ≪≫
      (kernelResolutionTensorModelIso A D F (BimoduleTensor.compose A F E D Q P) R).symm
  exact Localization.liftNatIso (moduleToDerived A D) (moduleQuasiIso A D)
    (moduleToDerived A D ⋙ G) (moduleToDerived A D ⋙ H) G H e

end SerrePositivity.DifferentialGraded.Morita
