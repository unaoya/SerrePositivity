module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionKFlatNaturality

/-! # 全導来入力上の通常kernel合成比較の自然性

## 概要
右相対K-flatな最初のkernelと任意の後のkernelの作用合成比較を、両kernelの射に自然にする。

## 方針
解像度モデルとの比較squareを合成し、指定主局所化からの自然変換の一意性を使う。

## 規約と注意
局所Hom K-flat条件は不要。kernelの主局所化に関する自然性は別途降ろす。

## 使われ方
U16aの全導来kernel合成比較をkernel射に自然な族にまとめるための接続。
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
  {P P' : BimoduleCategory A E D} {Q Q' : BimoduleCategory A F E}
  (f : P ⟶ P') (g : Q ⟶ Q')
local notation "P₀" => BimoduleCategory.underlying A E D P
local notation "P₁" => BimoduleCategory.underlying A E D P'
local notation "Q₀" => BimoduleCategory.underlying A F E Q
local notation "Q₁" => BimoduleCategory.underlying A F E Q'
local notation "R" => moduleCanonicalProjectiveResolution A D
local notation "S" => moduleCanonicalProjectiveResolution A E

/-- 二つの作用射の水平合成と、最初の作用の解像度モデル比較が可換。 -/
lemma kernelCompositionSourceModelSquare (M : ModuleCategory A D) :
    (NatTrans.hcomp (kernelResolutionDerivedTensorMap A D E R f)
        (kernelResolutionDerivedTensorMap A E F S g)).app ((moduleToDerived A D).obj M) ≫
        (kernelDerivedTensorOnBimodule A E F Q₁).map
          ((kernelResolutionTensorModelIso A D E P₁ R).hom.app M) =
      (kernelDerivedTensorOnBimodule A E F Q₀).map
          ((kernelResolutionTensorModelIso A D E P₀ R).hom.app M) ≫
        (NatTrans.hcomp (kernelResolutionTensorModelMap A D E f R)
          (kernelResolutionDerivedTensorMap A E F S g)).app M := by
  have hf := congrArg (kernelDerivedTensorOnBimodule A E F Q₁).map
    (NatTrans.congr_app (kernelResolutionTensorModelIso_kernel_naturality A D E f R) M)
  simp only [NatTrans.comp_app, whiskerLeft_app, Functor.map_comp] at hf
  have hg := (kernelResolutionDerivedTensorMap A E F S g).naturality
    ((kernelResolutionTensorModelIso A D E P₀ R).hom.app M)
  simp only [NatTrans.hcomp_app, Category.assoc]
  slice_lhs 2 3 => erw [hf]
  slice_lhs 1 2 => erw [← hg]
  rw [Category.assoc]
  rfl

/-- 通常kernelの主導来作用の合成比較は、両kernelの閉零射に自然。 -/
lemma kernelDerivedTensorOnBimoduleCompositionIso_kernel_naturality
    (hP : Bimodule.rightRelativeKFlat A E D P₀)
    (hP' : Bimodule.rightRelativeKFlat A E D P₁) :
    NatTrans.hcomp (kernelResolutionDerivedTensorMap A D E R f)
        (kernelResolutionDerivedTensorMap A E F S g) ≫
        (kernelDerivedTensorOnBimoduleCompositionIso A D E F P₁ Q₁ hP').hom =
      (kernelDerivedTensorOnBimoduleCompositionIso A D E F P₀ Q₀ hP).hom ≫
        kernelResolutionDerivedTensorMap A D F R (BimoduleTensor.composeMap A F E D g f) := by
  apply Localization.natTrans_ext (moduleToDerived A D) (moduleQuasiIso A D)
  intro M
  have hs := kernelCompositionSourceModelSquare A D E F f g M
  have ht := NatTrans.congr_app (kernelResolutionTensorModelIso_kernel_naturality A D F
    (BimoduleTensor.composeMap A F E D g f) R) M
  simp only [NatTrans.comp_app, whiskerLeft_app] at ht
  change (kernelResolutionDerivedTensorMap A D F R
      (BimoduleTensor.composeMap A F E D g f)).app ((moduleToDerived A D).obj M) ≫
      (kernelResolutionTensorModelIso A D F (BimoduleTensor.compose A F E D Q₁ P₁) R).hom.app M =
    (kernelResolutionTensorModelIso A D F (BimoduleTensor.compose A F E D Q₀ P₀) R).hom.app M ≫
      (kernelResolutionTensorModelMap A D F (BimoduleTensor.composeMap A F E D g f) R).app M at ht
  have hm := NatTrans.congr_app
    (kernelResolutionTensorCompositionIso_kernel_naturality A D E F f g hP hP' R) M
  simp only [NatTrans.comp_app] at hm
  simp only [NatTrans.comp_app]
  rw [kernelDerivedTensorOnBimoduleCompositionIso_hom_app,
    kernelDerivedTensorOnBimoduleCompositionIso_hom_app]
  apply (cancel_mono ((kernelResolutionTensorModelIso A D F
    (BimoduleTensor.compose A F E D Q₁ P₁) R).hom.app M)).1
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  slice_rhs 4 5 => erw [ht]
  slice_rhs 3 4 => erw [Iso.inv_hom_id_app]
  slice_lhs 1 2 => erw [hs]
  slice_lhs 2 3 => erw [hm]
  simp only [Category.id_comp]

end SerrePositivity.DifferentialGraded.Morita
