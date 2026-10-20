module
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionTriangle
public import SerrePositivity.KST.SConstruction.DGModuleExtensionRightUnitEvaluation

/-! # 元の実 Perf 延長の右恒等入力
概要：右恒等入力の元の Perf 合成比較が、出力における同じ単位射を回収する。
方針：全加群への包含で元の比較を回収し、包含の忠実性で射の等号を反映する。
規約：入力等号の移送と元の比較射を保持する。使われ方：関手的 Perf の両単位法則。
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

/-- 元の実 Perf 合成比較の右恒等入力は、出力における同じ実単位射。 -/
lemma perfectDGExtensionCompositionAt_comp_id (F : DGFunctor A D E)
    (M : PerfectDGModule A D) :
    (perfectDGExtensionCompositionAt A D E E F (DGFunctor.id E) M).hom ≫
        (perfectDGExtensionInputIso A D E (strictDGFunctor_comp_id F) M).hom =
      (perfectDGExtensionIdentityAt A E ((perfectDGExtension A D E F).obj M)).hom := by
  have : (perfectDGModuleInclusion A E Set.univ).onClosed.Faithful := by
    dsimp only [perfectDGModuleInclusion]
    infer_instance
  apply (perfectDGModuleInclusion A E Set.univ).onClosed.map_injective
  rw [Functor.map_comp, perfectDGExtensionCompositionAt_inclusion,
    perfectDGExtensionInputIso_inclusion, perfectDGExtensionIdentityAt_inclusion]
  exact dgModuleExtensionCompositionAt_comp_id A D E F M.val

end SerrePositivity.KST.SConstruction
