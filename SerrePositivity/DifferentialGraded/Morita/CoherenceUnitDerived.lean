module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceUnitClosed
public import SerrePositivity.DifferentialGraded.Morita.CoherenceProjectiveExt

/-! # 通常kernelの導来作用の右単位coherence

## 概要
恒等kernelを先に作用させる導来比較を、元のbimodule右単位子と整合させる。

## 方針
相対K-flat入力で増大を反転して通常単位図式へ帰着し、射影解像度から全入力へ拡張する。

## 規約と注意
局所Hom K-flat性や指定kernelの右相対K-flat性は不要。恒等kernelのK-flat性だけを使う。

## 使われ方
U16aの主導来kernel全体での単位coherenceへの計算入口。
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
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

/-- 相対K-flat入力での導来作用の右単位図式。 -/
lemma kernelDerivedTensorOnBimoduleCompositionIso_rightUnit_app
    (M : ModuleCategory A D)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M)) :
    (kernelDerivedTensorOnBimoduleCompositionIso A D D E (Bimodule.diagonal A D) P
        (Bimodule.diagonal_rightRelativeKFlat A D)).hom.app ((moduleToDerived A D).obj M) ≫
      (kernelResolutionDerivedTensorMap A D E (moduleCanonicalProjectiveResolution A D)
        (rightBimoduleUnitIso A E D P).hom).app ((moduleToDerived A D).obj M) =
    (kernelDerivedTensorOnBimodule A D E P).map
      ((kernelDerivedTensorOnBimoduleIdentityIso A D).hom.app ((moduleToDerived A D).obj M)) := by
  let LP := kernelDerivedTensorOnBimodule A D E P
  let aug := (kernelDerivedTensorAugmentation A D E P).app M
  have := kernelDerivedTensorAugmentation_isIso_of_relativeKFlat A D E P M hM
  apply (cancel_mono aug).1
  rw [Category.assoc]
  dsimp only [aug]
  erw [kernelDerivedTensorAugmentation_kernel_naturality A D E
    (rightBimoduleUnitIso A E D P).hom M]
  rw [← Category.assoc]
  erw [kernelDerivedTensorOnBimoduleCompositionIso_augmentation]
  simp only [Category.assoc]
  slice_lhs 3 4 => rw [← Functor.map_comp, kernelTensorCompositionClosedIso_rightUnit]
  have hn := (kernelDerivedTensorAugmentation A D E P).naturality
    ((kernelIdentityClosedIso A D).hom.app M)
  simp only [Functor.comp_map] at hn
  slice_lhs 2 3 => erw [← hn]
  slice_lhs 1 2 => rw [← Functor.map_comp, ← kernelDerivedTensorOnBimoduleIdentityIso_augmentation]
  rfl

/-- 導来作用の合成比較は、恒等kernelを先に作用させる右単位図式を満たす。 -/
lemma kernelDerivedTensorOnBimoduleCompositionIso_rightUnit :
    (kernelDerivedTensorOnBimoduleCompositionIso A D D E (Bimodule.diagonal A D) P
        (Bimodule.diagonal_rightRelativeKFlat A D)).hom ≫
      kernelResolutionDerivedTensorMap A D E (moduleCanonicalProjectiveResolution A D)
        (rightBimoduleUnitIso A E D P).hom =
    whiskerRight (kernelDerivedTensorOnBimoduleIdentityIso A D).hom
        (kernelDerivedTensorOnBimodule A D E P) ≫
      (Functor.leftUnitor (kernelDerivedTensorOnBimodule A D E P)).hom := by
  apply kernelActionNatTrans_ext_projective A D
  intro M hM
  simp only [NatTrans.comp_app, whiskerRight_app, Functor.leftUnitor_hom_app]
  erw [Category.comp_id]
  exact kernelDerivedTensorOnBimoduleCompositionIso_rightUnit_app A D E P M
    (moduleHomotopicallyProjective_relativeKFlat A D hM)

end SerrePositivity.DifferentialGraded.Morita
