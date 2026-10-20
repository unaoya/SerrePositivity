module
public import SerrePositivity.KST.SConstruction.DGModuleExtensionRightUnitTensor

/-! # 元の実加群延長の右単位法則
概要：右恒等 dg 入力の実合成比較を、同じ出力対象の実単位比較と照合する。
方針：全 Hom 自然な tensor 単位の式を評価し、元の対象別比較射を回収する。
規約：入力の等号移送を保持する。使われ方：実 Perf 延長の右単位への制限。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]

/-- 元の右恒等入力の実合成比較は、出力における同じ実恒等延長の単位射。 -/
lemma dgModuleExtensionCompositionAt_comp_id (F : DGFunctor A D E) (M : RightModule A D) :
    (dgModuleExtensionCompositionAt A D E E F (DGFunctor.id E) M).hom ≫
        (dgModuleExtensionInputIso A D E (strictDGFunctor_comp_id F) M).hom =
      (dgModuleExtensionIdentityAt A E ((dgModuleExtension A D E F).obj M)).hom := by
  have h := congrArg ((BimoduleCategory.evaluation A E (RightModule A D) M).map)
    (dgModuleExtensionCompositionTensorIso_comp_id A D E F)
  simp only [Functor.map_comp] at h
  rw [dgModuleExtensionInputIso_tensor_evaluation] at h
  have hu := congrArg Iso.hom (dgBimoduleDiagonalUnitIso_extension_evaluation A D E
    (functorGraph A E E (DGFunctor.id E)) (functorGraph_identity A E) F M)
  change (BimoduleCategory.evaluation A E (RightModule A D) M).map
      (dgBimoduleDiagonalUnitIso A E (RightModule A D)
        (functorGraph A E E (DGFunctor.id E)) (functorGraph_identity A E)
        (dgModuleExtension A D E F)).hom =
    (dgModuleExtensionIdentityAt A E ((dgModuleExtension A D E F).obj M)).hom at hu
  exact h.trans hu

end SerrePositivity.KST.SConstruction
