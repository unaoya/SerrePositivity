module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceUnitDerived
public import SerrePositivity.DifferentialGraded.Morita.CoherenceComposition

/-! # 主導来kernel作用の右単位coherence

## 概要
公開された主導来kernel作用の合成・恒等比較が、U12e-localの右単位子と整合する。

## 方針
恒等kernelは右K-flatなので同じ合成モデルを使い、通常kernel計算から主局所化の任意対象へ運ぶ。

## 規約と注意
合成に必要な始域Dの局所Hom K-flat性だけを要求し、指定kernelの列の射影性は要求しない。

## 使われ方
U16aの作用coherenceとU16dのPerfへの制限。
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

/-- 主導来右単位子の作用と、通常右単位子の作用を同じ合成モデルで比較する。 -/
lemma kernelCompositionTargetIso_rightUnit (hD : localHomKFlat A D) (P : BimoduleCategory A E D) :
    (kernelDerivedTensorFunctor A D E).map
        ((derivedBimoduleRightUnitIso A E D hD).hom.app ((bimoduleToDerived A E D).obj P)) ≫
      (kernelDerivedTensorOnBimoduleIso A D E P).hom =
    (kernelCompositionTargetIso A D D E hD (rightKFlatDiagonal A D) P).hom ≫
      kernelResolutionDerivedTensorMap A D E (moduleCanonicalProjectiveResolution A D)
        (rightBimoduleUnitIso A E D (BimoduleCategory.underlying A E D P)).hom := by
  rw [derivedBimoduleRightUnitIso_base_app, Functor.map_comp, Category.assoc]
  erw [kernelDerivedTensorOnBimoduleIso_naturality A D E
    (rightBimoduleUnitIso A E D (BimoduleCategory.underlying A E D P)).hom]
  exact (Category.assoc _ _ _).symm

/-- 恒等kernelを先に作用させる公開合成比較は、主導来右単位子と整合する。 -/
lemma kernelCompositionIso_rightUnit (hD : localHomKFlat A D) (P : Kernel A D E) :
    (kernelCompositionIso A D D E hD (kernelIdentity A D) P).hom ≫
      (kernelDerivedTensorFunctor A D E).map ((derivedBimoduleRightUnitIso A E D hD).hom.app P) =
    whiskerRight (kernelIdentityIso A D).hom (kernelDerivedTensor A D E P) ≫
      (Functor.leftUnitor (kernelDerivedTensor A D E P)).hom := by
  obtain ⟨⟨Q⟩⟩ := P
  let eQ := kernelDerivedTensorOnBimoduleIso A D E Q
  let eΔ := kernelDerivedTensorOnBimoduleIso A D D (rightKFlatDiagonal A D).obj
  apply (cancel_mono eQ.hom).1
  rw [Category.assoc]
  erw [kernelCompositionTargetIso_rightUnit A D E hD Q]
  erw [kernelCompositionIso_model A D D E hD (rightKFlatDiagonal A D) Q]
  dsimp only [kernelCompositionModelIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc]
  slice_lhs 3 5 => rw [Iso.inv_hom_id_assoc]
  slice_lhs 2 3 => erw [kernelDerivedTensorOnBimoduleCompositionIso_rightUnit A D E
    (BimoduleCategory.underlying A E D Q)]
  apply NatTrans.ext
  funext X
  simp only [NatTrans.comp_app, NatIso.hcomp_hom, NatTrans.hcomp_app, whiskerRight_app,
    Functor.leftUnitor_hom_app]
  erw [Category.comp_id, Category.id_comp]
  change (eQ.hom.app _ ≫ (kernelDerivedTensorOnBimodule A D E
      (BimoduleCategory.underlying A E D Q)).map (eΔ.hom.app X)) ≫
      (kernelDerivedTensorOnBimodule A D E (BimoduleCategory.underlying A E D Q)).map
        ((kernelDerivedTensorOnBimoduleIdentityIso A D).hom.app X) =
    (kernelDerivedTensor A D E ((bimoduleToDerived A E D).obj Q)).map
      ((kernelIdentityIso A D).hom.app X) ≫ eQ.hom.app X
  rw [Category.assoc, ← Functor.map_comp]
  exact (eQ.hom.naturality ((kernelIdentityIso A D).hom.app X)).symm

end SerrePositivity.DifferentialGraded.Morita
