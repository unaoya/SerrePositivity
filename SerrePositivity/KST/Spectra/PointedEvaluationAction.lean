module

public import SerrePositivity.KST.Spectra.PointedIhomActionComposition
public import SerrePositivity.KST.Spectra.PointedIhomParameterRestriction
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSymmetry
public import SerrePositivity.KST.Spectra.PointedHomTransposeComponents

/-!
概要：普遍評価による後合成を、内部 Hom の作用と源の元の比較射へ書き直す。
方針：二つの curry 変数を交換し、元の合成の二重評価を比較する。
規約：Kan 性不要。使われ方：実評価側の源単位区間の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.PointedMapping

private lemma closedEvaluationPost_exchange {C : Type*} [Category C]
    [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
    {K U E V : C} (q : U ⟶ (ihom K).obj E) :
    curry (curry ((β_ U K).hom ≫ uncurry q) ▷ (ihom E).obj V ≫ comp U E V) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso U K V).inv =
    curry (q ▷ (ihom E).obj V ≫ comp K E V) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.hom_eq_inv]
  apply uncurry_injective
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left,
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.uncurry_uncurry_hom]
  simp only [uncurry_curry]
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_right_assoc]
  rw [← whiskerLeft_comp_assoc,
    ← uncurry_eq (curry (curry ((β_ U K).hom ≫ uncurry q) ▷ (ihom E).obj V ≫ comp U E V)),
    uncurry_curry]
  rw [uncurry_natural_left]
  simp only [comp_eq, whiskerLeft_comp, Category.assoc,
    whiskerLeft_curry_ihom_ev_app, uncurry_curry, compTranspose_eq]
  rw [associator_inv_naturality_middle_assoc, associator_inv_naturality_middle_assoc]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    tensorRight, Functor.flip, curriedTensor, Category.assoc, Iso.hom_inv_id_assoc]
  simp only [← comp_whiskerRight_assoc, ← uncurry_eq, uncurry_curry]
  rw [SymmetricCategory.symmetry_assoc]


/-- 同じ普遍評価の後合成は、内部 Hom の作用に元の比較射を前合成したもの。 -/
lemma evaluationPost_exchange {K U E V : PointedSimplicialSet.{u}}
    (q : U ⟶ (ihom K).obj E) :
    curry (transpose q ▷ PointedObject.basedHom E V ≫ MonoidalClosed.comp U E V) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso U K V).inv =
    ihomAction K E V ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed q (PointedObject.basedHom K V) := by
  rw [ihomParameterAction_eq_curry]
  exact closedEvaluationPost_exchange q

/-- 作用を比較射で評価してから制限しても、元の比較射の同じ制限を作用へ入力する。 -/
@[reassoc]
lemma ihomParameterAction_restrict_input {K' K U E V : PointedSimplicialSet.{u}}
    (i : K' ⟶ K) (q : U ⟶ PointedObject.basedHom K E) :
    (ihomAction K E V ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed q (PointedObject.basedHom K V)) ≫
      (ihom U).map (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i V) =
    ihomAction K' E V ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (q ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i E) (PointedObject.basedHom K' V) := by
  have hn := (MonoidalClosed.pre q).naturality (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i V)
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hn
  rw [Category.assoc, ← hn, ← Category.assoc, ihomAction_restrict,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp]


/-- 同じ作用の評価は、元の比較の uncurry への前合成と反復 curry の同型である。 -/
lemma ihomParameterAction_eq_adjoint_pre {K U E V : PointedSimplicialSet.{u}}
    (q : U ⟶ PointedObject.basedHom K E) :
    ihomAction K E V ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed q (PointedObject.basedHom K V) =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (uncurry q) V ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K U V).hom := by
  have hn := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorSource.natural_pre_right K q V
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hn
  rw [ihomAction, Category.assoc]
  erw [← hn]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp]
  rfl

end SerrePositivity.KST.Spectra.PointedMapping
