module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitCompositionPoints
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitCompositionUnit
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentUnits
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt

/-!
# 元の恒等列の標準射と余極限の単位点

概要：恒等列の像を元の空語の単位点へ照合し、元の合成の左右単位則を回収する。
方針：空語から一列への標準射と元の余錐条件を使う。
規約：元の恒等射・標準射・全次数の点を保持する。
使われ方：切断で挿入された恒等列を元の hammock の点から除く。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]

lemma empty_to_identity (X : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.fromEmpty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) (𝟙 X) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext
  · intro j
    change Fin 2 at j
    cases j using Fin.cases with
    | zero => rfl
    | succ j => rfl
  · intro j
    change Fin 1 at j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    apply heq_of_eq
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W X) (0 : Fin 1) (0 : Fin 1) _ _ = 𝟙 X
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_refl .forward (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W X) 0 _

lemma empty_to_identity_simplex (X : C) (n : SimplexCategoryᵒᵖ) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphUnit W X).app n PUnit.unit) ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.fromEmpty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowSimplex W (𝟙 X) n := by
  change ((Functor.const (Fin (n.unop.len + 1))).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W X)) ⋙ _ = _
  refine CategoryTheory.Functor.ext (F := _)
    (G := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowSimplex W (𝟙 X) n) (fun _ => empty_to_identity W X) ?_
  intro d e f
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.fromEmpty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward))).map
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W X)) = eqToHom _ ≫ 𝟙 _ ≫ eqToHom _
  rw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, eqToHom_trans, eqToHom_refl]

lemma arrowPoint_identity (X : C) (n : SimplexCategoryᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint W (𝟙 X) n = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W X).app n PUnit.unit := by
  have hι := congrArg (fun k => k.app n ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphUnit W X).app n PUnit.unit))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion_naturality W X X (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.fromEmpty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)))
  have hs := empty_to_identity_simplex W X n
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X X (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)).app n (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowSimplex W (𝟙 X) n) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X X _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty).app n ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphUnit W X).app n PUnit.unit)
  exact (congrArg (fun F => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X X (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)).app n F) hs).symm.trans hι

lemma composePoint_identity_left {X Y : C} {n : SimplexCategoryᵒᵖ}
    (p : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y).obj n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W X X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint W (𝟙 X) n) p = p := by
  rw [arrowPoint_identity]
  exact congrArg (fun f => f.app n (PUnit.unit, p)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition_left_unit W X Y)

lemma composePoint_identity_right {X Y : C} {n : SimplexCategoryᵒᵖ}
    (p : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y).obj n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W X Y Y p (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint W (𝟙 Y) n) = p := by
  rw [arrowPoint_identity]
  exact congrArg (fun f => f.app n (p, PUnit.unit)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition_right_unit W X Y)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
