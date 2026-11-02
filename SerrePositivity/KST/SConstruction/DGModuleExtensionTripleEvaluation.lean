module
public import SerrePositivity.KST.SConstruction.DGModuleExtensionTripleTensor
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGModuleExtensionEvaluationTransport
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGModuleExtensionInputTransport

/-! # 元の実加群延長の三重比較
概要：三重 tensor 比較を評価し、元の実加群の比較射の等号へ移す。
方針：右端の評価と閉零射作用を回収し、元の入力等号の移送を保つ。
規約：大きい全加群型の smallness を要求しない。使われ方：実延長の三重比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z q
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) (T : Type z) (U : Type q)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  [DGCategory A T] [Small.{u} T] [DGCategory A U] [Small.{u} U]
  (F : DGFunctor A D E) (G : DGFunctor A E T) (H : DGFunctor A T U)
local notation "P" => functorGraph A T U H
local notation "Q" => functorGraph A E T G

/-- 外側の tensor 比較を評価すると、元の実延長の同じ対象別比較となる。 -/
lemma dgModuleExtension_outer_composition_evaluation (M : RightModule A D) :
    (BimoduleCategory.evaluation A U (RightModule A D) M).map
      ((BimoduleTensor.associatorIso A U T E (RightModule A D) P Q
          (dgModuleExtension A D E F)).inv ≫
        BimoduleTensor.composeMap A U E (RightModule A D)
          (dgFunctorGraphCompositionIso A E T U G H).hom
          (𝟙 (BimoduleCategory.of A E (RightModule A D) (dgModuleExtension A D E F)))) =
    (dgModuleExtensionCompositionAt A E T U G H ((dgModuleExtension A D E F).obj M)).hom := by
  apply moduleMorphism_ext
  intro u
  change (BimoduleCategory.valueEvaluation A U (RightModule A D) u M).map
    ((BimoduleTensor.associatorIso A U T E (RightModule A D) P Q
      (dgModuleExtension A D E F)).inv ≫
      BimoduleTensor.composeMap A U E (RightModule A D)
        (dgFunctorGraphCompositionIso A E T U G H).hom
        (𝟙 (BimoduleCategory.of A E (RightModule A D) (dgModuleExtension A D E F)))) =
    (BimoduleCategory.valueEvaluation A U (RightModule A E) u
      ((dgModuleExtension A D E F).obj M)).map
      (dgModuleExtensionCompositionTensorIso A E T U G H).hom
  simp only [dgModuleExtensionCompositionTensorIso, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, dgModuleGraphTensorFunctor_map,
    CategoryTheory.Functor.map_comp, BimoduleTensor.associatorIso_inv_value_eval,
    BimoduleTensor.composeMap_value_eval]
  rw [dgTensor_associator_value_evaluation A U T E (RightModule A D) P Q
    (dgModuleExtension A D E F) u M]
  rw [dgTensor_first_value_evaluation A U E (RightModule A D)
    (dgFunctorGraphCompositionIso A E T U G H).hom (dgModuleExtension A D E F) u M]

/-- 同じ元の三重実延長比較の二経路は、入力の結合等号の移送を保って一致する。 -/
lemma dgModuleExtensionCompositionAt_assoc (M : RightModule A D) :
    (dgModuleExtension A T U H).onClosed.map
        (dgModuleExtensionCompositionAt A D E T F G M).hom ≫
      (dgModuleExtensionCompositionAt A D T U (F.comp G) H M).hom ≫
      (dgModuleExtensionInputIso A D U (strictDGFunctor_comp_assoc F G H) M).hom =
    (dgModuleExtensionCompositionAt A E T U G H ((dgModuleExtension A D E F).obj M)).hom ≫
      (dgModuleExtensionCompositionAt A D E U F (G.comp H) M).hom := by
  have h := congrArg ((BimoduleCategory.evaluation A U (RightModule A D) M).map)
    (dgModuleExtensionCompositionTensorIso_assoc A D E T U F G H)
  simp only [CategoryTheory.Functor.map_comp] at h
  rw [dgModuleExtension_second_map_evaluation,
    dgModuleExtensionInputIso_tensor_evaluation] at h
  have ho := dgModuleExtension_outer_composition_evaluation A D E T U F G H M
  simp only [CategoryTheory.Functor.map_comp] at ho
  have hp := congrArg (fun k => k ≫
    (dgModuleExtensionCompositionAt A D E U F (G.comp H) M).hom) ho
  simp only [Category.assoc] at hp
  exact h.trans hp

end SerrePositivity.KST.SConstruction
