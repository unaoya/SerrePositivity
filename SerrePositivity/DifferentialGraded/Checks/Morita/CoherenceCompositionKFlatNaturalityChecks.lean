module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionKernel
public import SerrePositivity.DifferentialGraded.Checks.Morita.CoherenceCompositionChecks

/-! # K-flatモデルの作用合成squareと主局所化計算の監査

## 概要
任意の指定入力解像度族と両kernelの射に対する、モデル上の合成自然性を確認する。

## 方針
局所Hom条件を追加せずにsquareを検査し、公開計算定理と自然性を直接監査する。

## 規約と注意
最初のkernelの両端モデルに右相対K-flat性を要求する。全導来kernel射への降下は未完。

## 使われ方
U16aの全導来kernel自然性への接続を再現する検査入口。
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

example {P P' : BimoduleCategory A E D} {Q Q' : BimoduleCategory A F E}
    (f : P ⟶ P') (g : Q ⟶ Q')
    (hP : Bimodule.rightRelativeKFlat A E D (BimoduleCategory.underlying A E D P))
    (hP' : Bimodule.rightRelativeKFlat A E D (BimoduleCategory.underlying A E D P'))
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    NatTrans.hcomp (kernelResolutionTensorModelMap A D E f R)
        (kernelResolutionDerivedTensorMap A E F (moduleCanonicalProjectiveResolution A E) g) ≫
        (kernelResolutionTensorCompositionIso A D E F
          (BimoduleCategory.underlying A E D P') (BimoduleCategory.underlying A F E Q') hP' R).hom =
      (kernelResolutionTensorCompositionIso A D E F
          (BimoduleCategory.underlying A E D P) (BimoduleCategory.underlying A F E Q) hP R).hom ≫
        kernelResolutionTensorModelMap A D F (BimoduleTensor.composeMap A F E D g f) R :=
  kernelResolutionTensorCompositionIso_kernel_naturality A D E F f g hP hP' R

#print axioms kernelResolutionTensorCompositionIso_hom_app
#print axioms kernelResolutionTensorCompositionIso_kernel_naturality
#print axioms kernelDerivedTensorOnBimoduleCompositionIso_hom_app
