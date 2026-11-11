module

public import SerrePositivity.KST.Spectra.PointedIhomIntervalAction
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorSource

/-!
概要：内部 Hom の関手作用と、元の二つの源の制限の厳密な自然性。
方針：反復 curry の源自然性と評価の自然性で同じ前合成を比較する。
規約：Kan 性不要。使われ方：単位の実三角形の三辺を全 Hom の構造制限へ照合する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 標的へ入力する射の源制限は、同じ内部 Hom の入力の後合成に対応する。 -/
lemma ihomAction_pre (A : PointedSimplicialSet.{u})
    {E' E : PointedSimplicialSet.{u}} (j : E' ⟶ E) (V : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j V ≫ ihomAction A E' V =
    ihomAction A E V ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed ((ihom A).map j) (PointedObject.basedHom A V) := by
  have hn := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorSource.natural_pre_right A ((ihom A).map j) V
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hn
  simp only [ihomAction, Category.assoc]
  erw [← hn]
  rw [← Category.assoc, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp]
  have he : A ◁ (ihom A).map j ≫ (ihom.ev A).app E = (ihom.ev A).app E' ≫ j :=
    (ihom.ev A).naturality j
  exact congrArg (fun k => _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed k V ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso A (PointedObject.basedHom A E') V).hom) he.symm

/-- 内部 Hom の源制限は、その入力と出力に同じ制限を施す自然変換となる。 -/
lemma ihomAction_restrict {A' A : PointedSimplicialSet.{u}} (i : A' ⟶ A)
    (E V : PointedSimplicialSet.{u}) :
    ihomAction A E V ≫
      (ihom (PointedObject.basedHom A E)).map (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i V) =
    ihomAction A' E V ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i E) (PointedObject.basedHom A' V) := by
  have hl := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorSource.natural_pre_left i (PointedObject.basedHom A E) V
  have hr := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorSource.natural_pre_right A' (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i E) V
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hl hr
  simp only [ihomAction, Category.assoc]
  erw [← hl, ← hr]
  rw [← Category.assoc, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp]
  have he : A' ◁ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i E ≫ (ihom.ev A').app E =
      i ▷ PointedObject.basedHom A E ≫ (ihom.ev A).app E := by
    simp only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
    exact MonoidalClosed.id_tensor_pre_app_comp_ev i E
  rw [he]

end SerrePositivity.KST.Spectra.PointedMapping
