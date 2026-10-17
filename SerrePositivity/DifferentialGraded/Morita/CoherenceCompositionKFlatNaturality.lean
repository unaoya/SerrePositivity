module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionKFlat
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionNaturality
public import Mathlib.Tactic.CategoryTheory.Slice

/-! # K-flat解像度モデル上の導来作用合成のkernel自然性

## 概要
右相対K-flatな最初のkernelの任意の射と、後のkernelの任意の射に関する合成squareを証明する。

## 方針
後の作用の増大のkernel自然性・入力自然性と通常合成の自然性を同じ成分で接続する。

## 規約と注意
任意の入力射影解像度族を使う。局所Hom条件は不要。主導来kernel射への降下は別途行う。

## 使われ方
U16aのkernelCompositionIsoを全kernel射に自然な族へ運ぶモデル上の接続。
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

/-- 解像度モデル上の合成比較の成分を、二つの既存の自然な比較射で計算する。 -/
lemma kernelResolutionTensorCompositionIso_hom_app
    (P : Bimodule A E D) (Q : Bimodule A F E)
    (hP : Bimodule.rightRelativeKFlat A E D P)
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (M : ModuleCategory A D) :
    (kernelResolutionTensorCompositionIso A D E F P Q hP R).hom.app M =
      (kernelDerivedTensorAugmentation A E F Q).app
          ((kernelTensor A D E P).onClosed.obj (R M).obj) ≫
        (moduleToDerived A F).map
          ((kernelTensorCompositionClosedIso A D E F P Q).hom.app (R M).obj) := rfl

/-- 自然な解像度モデル上の合成比較は、両kernelの閉零射に自然。 -/
lemma kernelResolutionTensorCompositionIso_kernel_naturality
    (hP : Bimodule.rightRelativeKFlat A E D P₀)
    (hP' : Bimodule.rightRelativeKFlat A E D P₁)
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    NatTrans.hcomp (kernelResolutionTensorModelMap A D E f R)
        (kernelResolutionDerivedTensorMap A E F (moduleCanonicalProjectiveResolution A E) g) ≫
        (kernelResolutionTensorCompositionIso A D E F P₁ Q₁ hP' R).hom =
      (kernelResolutionTensorCompositionIso A D E F P₀ Q₀ hP R).hom ≫
        kernelResolutionTensorModelMap A D F (BimoduleTensor.composeMap A F E D g f) R := by
  apply NatTrans.ext
  funext M
  have hi := (kernelDerivedTensorAugmentation A E F Q₁).naturality
    ((kernelTensorMap A D E f).app (R M).obj)
  simp only [Functor.comp_map] at hi
  have hk := kernelDerivedTensorAugmentation_kernel_naturality A E F g
    ((kernelTensor A D E P₀).onClosed.obj (R M).obj)
  have hc := congrArg (moduleToDerived A F).map
    (NatTrans.congr_app (kernelTensorCompositionClosedIso_kernel_naturality A D E F f g)
      (R M).obj)
  simp only [NatTrans.comp_app, NatTrans.hcomp_app, Functor.map_comp] at hc
  simp only [NatTrans.comp_app, NatTrans.hcomp_app, Category.assoc]
  rw [kernelResolutionTensorCompositionIso_hom_app,
    kernelResolutionTensorCompositionIso_hom_app]
  dsimp only [kernelResolutionTensorModelMap]
  slice_lhs 2 3 => erw [hi]
  slice_lhs 1 2 => erw [hk]
  simp only [Category.assoc]
  simpa only [Category.assoc] using congrArg (fun k =>
    (kernelDerivedTensorAugmentation A E F Q₀).app
    ((kernelTensor A D E P₀).onClosed.obj (R M).obj) ≫ k) hc

/-- 全導来入力へ延長した通常kernel合成比較は、元の入力では指定モデルの比較を計算する。 -/
lemma kernelDerivedTensorOnBimoduleCompositionIso_hom_app
    (P : Bimodule A E D) (Q : Bimodule A F E)
    (hP : Bimodule.rightRelativeKFlat A E D P) (M : ModuleCategory A D) :
    (kernelDerivedTensorOnBimoduleCompositionIso A D E F P Q hP).hom.app
        ((moduleToDerived A D).obj M) =
      ((kernelDerivedTensorOnBimodule A E F Q).map
          ((kernelResolutionTensorModelIso A D E P
            (moduleCanonicalProjectiveResolution A D)).hom.app M) ≫
        (kernelResolutionTensorCompositionIso A D E F P Q hP
          (moduleCanonicalProjectiveResolution A D)).hom.app M) ≫
        (kernelResolutionTensorModelIso A D F (BimoduleTensor.compose A F E D Q P)
          (moduleCanonicalProjectiveResolution A D)).inv.app M := by
  simp only [kernelDerivedTensorOnBimoduleCompositionIso, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app]
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, whiskerRight_app, Functor.associator_inv_app]
  erw [Category.id_comp, Category.comp_id, Category.id_comp]
  rw [Category.assoc]

end SerrePositivity.DifferentialGraded.Morita
