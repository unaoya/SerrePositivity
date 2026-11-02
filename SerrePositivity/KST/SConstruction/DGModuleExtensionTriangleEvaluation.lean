module
public import SerrePositivity.KST.SConstruction.DGModuleExtensionTriangle
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGModuleExtensionInputTransport

/-! # 元の実加群延長の対象別単位三角
概要：全 Hom 自然な三角を、元の実延長の対象別比較射の等号に移す。
方針：graph 入力等号の tensor 評価と、元の閉零射作用の回収を使う。
規約：既存の合成・単位比較を変更しない。使われ方：実 Perf 延長の三角への制限。
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

/-- 元の実延長の合成比較と単位比較の、同じ対象・同じ射による三角。 -/
lemma dgModuleExtensionCompositionAt_id (F : DGFunctor A D E) (M : RightModule A D) :
    (dgModuleExtensionCompositionAt A D D E (DGFunctor.id D) F M).hom ≫
        (dgModuleExtensionInputIso A D E (strictDGFunctor_id_comp F) M).hom =
      (dgModuleExtension A D E F).onClosed.map (dgModuleExtensionIdentityAt A D M).hom := by
  have h := congrArg ((BimoduleCategory.evaluation A E (RightModule A D) M).map)
    (dgModuleExtensionCompositionTensorIso_id A D E F)
  simp only [Functor.map_comp] at h
  rw [dgModuleExtensionInputIso_tensor_evaluation,
    dgModuleExtension_second_map_evaluation] at h
  have hu := congrArg Iso.hom (dgModuleExtensionIdentityTensorIso_evaluation A D M)
  change (BimoduleCategory.evaluation A D (RightModule A D) M).map
    (dgModuleExtensionIdentityTensorIso A D).hom = (dgModuleExtensionIdentityAt A D M).hom at hu
  rw [hu] at h
  exact h

end SerrePositivity.KST.SConstruction
