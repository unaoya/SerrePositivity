module

public import SerrePositivity.KST.Spectra.PointedEvaluationAction
public import SerrePositivity.KST.Spectra.PointedRelativeTransposePaths

/-!
概要：パラメータ族への内部 Hom の作用を、元の族の転置とパラメータ交換で表示する。
方針：二度評価し、元の評価と braiding の自然性を比較する。
規約：Kan 性不要。使われ方：全列作用の両端を元の実評価へ戻す厳密座標。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.PointedMapping

private lemma closedParameterAction {C : Type*} [Category C] [MonoidalCategory C]
    [SymmetricCategory C] [MonoidalClosed C] {A K E V : C} (a : A ⟶ (ihom E).obj V) :
    (ihom K).map (curry ((β_ A E).hom ≫ uncurry a)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K A V).hom =
    curry ((β_ A ((ihom K).obj E)).hom ≫ uncurry (a ≫ curry (comp K E V))) := by
  apply uncurry_injective
  apply uncurry_injective
  simp only [uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.uncurry_uncurry_hom, uncurry_curry]
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_right_assoc]
  have hev := congrArg (fun f => A ◁ f)
    ((ihom.ev K).naturality (curry ((β_ A E).hom ≫ uncurry a)))
  change A ◁ (K ◁ (ihom K).map (curry ((β_ A E).hom ≫ uncurry a)) ≫
      (ihom.ev K).app ((ihom A).obj V)) =
    A ◁ ((ihom.ev K).app E ≫ curry ((β_ A E).hom ≫ uncurry a)) at hev
  simp only [whiskerLeft_comp] at hev
  rw [← Category.assoc (A ◁ K ◁ (ihom K).map (curry ((β_ A E).hom ≫ uncurry a))),
    hev, Category.assoc]
  rw [← uncurry_eq (curry ((β_ A E).hom ≫ uncurry a)), uncurry_curry]
  rw [comp_eq, uncurry_curry, compTranspose_eq]
  rw [associator_inv_naturality_right_assoc]
  erw [whisker_exchange_assoc]
  simp only [Functor.id_obj]
  rw [← uncurry_eq a]
  erw [BraidedCategory.braiding_naturality_right_assoc A ((ihom.ev K).app E)]
  have hs (T : C) : (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange K A T).hom ≫ (β_ A (K ⊗ T)).hom =
      K ◁ (β_ A T).hom ≫ (α_ K T A).inv := by
    simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      tensorRight, Functor.flip, curriedTensor, BraidedCategory.braiding_tensor_right_hom,
      Category.assoc, Iso.hom_inv_id_assoc]
    rw [← comp_whiskerRight_assoc, SymmetricCategory.symmetry, id_whiskerRight,
      Category.id_comp, Iso.inv_hom_id_assoc]
  simp only [Functor.comp_obj, tensorLeft, curriedTensor]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange K A ((ihom K).obj E)).hom,
    hs, Category.assoc]

/-- 元の入力族への作用は、その族の転置を mapping して同じパラメータを交換したもの。 -/
lemma transpose_ihomParameterAction {A K E V W : PointedSimplicialSet.{u}}
    (a : A ⟶ PointedObject.basedHom E V) (q : W ⟶ PointedObject.basedHom K E) :
    transpose (q ≫ (ihom K).map (transpose a) ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K A V).hom) =
      a ≫ ihomAction K E V ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed q (PointedObject.basedHom K V) := by
  have h : (ihom K).map (transpose a) ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K A V).hom =
      transpose (a ≫ ihomAction K E V) := by
    rw [ihomAction_eq_curry_comp]
    exact closedParameterAction a
  erw [h]
  rw [transpose_pre_outer, transpose_transpose, Category.assoc]
  rfl

end SerrePositivity.KST.Spectra.PointedMapping
