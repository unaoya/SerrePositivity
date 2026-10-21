module

public import SerrePositivity.EInfinity.Hammock.ColimitCompositionPoints
public import SerrePositivity.EInfinity.Hammock.ColimitCompositionUnit
public import SerrePositivity.EInfinity.Hammock.SegmentUnits
public import SerrePositivity.EInfinity.Hammock.ZigzagExt

/-!
# 元の恒等列の標準射と余極限の単位点

概要：恒等列の像を元の空語の単位点へ照合し、元の合成の左右単位則を回収する。
方針：空語から一列への標準射と元の余錐条件を使う。
規約：元の恒等射・標準射・全次数の点を保持する。
使われ方：切断で挿入された恒等列を元の hammock の点から除く。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]

lemma empty_to_identity (X : C) :
    WordAction.obj (Word.fromEmpty (Word.single .forward)) (emptyObj W X) =
      ForwardZigzag.obj (W := W) (𝟙 X) := by
  apply Zigzag.object_ext
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
    change Segment.map .forward (emptyObj W X) (0 : Fin 1) (0 : Fin 1) _ _ = 𝟙 X
    exact Segment.map_refl .forward (emptyObj W X) 0 _

lemma empty_to_identity_simplex (X : C) (n : SimplexCategoryᵒᵖ) :
    ((graphUnit W X).app n PUnit.unit) ⋙
      WordAction.functor (Word.fromEmpty (Word.single .forward)) =
        arrowSimplex W (𝟙 X) n := by
  change ((Functor.const (Fin (n.unop.len + 1))).obj (emptyObj W X)) ⋙ _ = _
  refine CategoryTheory.Functor.ext (F := _)
    (G := arrowSimplex W (𝟙 X) n) (fun _ => empty_to_identity W X) ?_
  intro d e f
  change (WordAction.functor (Word.fromEmpty (Word.single .forward))).map
    (𝟙 (emptyObj W X)) = eqToHom _ ≫ 𝟙 _ ≫ eqToHom _
  rw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, eqToHom_trans, eqToHom_refl]

lemma arrowPoint_identity (X : C) (n : SimplexCategoryᵒᵖ) :
    arrowPoint W (𝟙 X) n = (colimitUnit W X).app n PUnit.unit := by
  have hι := congrArg (fun k => k.app n ((graphUnit W X).app n PUnit.unit))
    (graphInclusion_naturality W X X (Word.fromEmpty (Word.single .forward)))
  have hs := empty_to_identity_simplex W X n
  change (graphInclusion W X X (Word.single .forward)).app n (arrowSimplex W (𝟙 X) n) =
    (graphInclusion W X X Word.empty).app n ((graphUnit W X).app n PUnit.unit)
  exact (congrArg (fun F => (graphInclusion W X X (Word.single .forward)).app n F) hs).symm.trans hι

lemma composePoint_identity_left {X Y : C} {n : SimplexCategoryᵒᵖ}
    (p : (colimitGraph W X Y).obj n) :
    composePoint W X X Y (arrowPoint W (𝟙 X) n) p = p := by
  rw [arrowPoint_identity]
  exact congrArg (fun f => f.app n (PUnit.unit, p)) (colimitComposition_left_unit W X Y)

lemma composePoint_identity_right {X Y : C} {n : SimplexCategoryᵒᵖ}
    (p : (colimitGraph W X Y).obj n) :
    composePoint W X Y Y p (arrowPoint W (𝟙 Y) n) = p := by
  rw [arrowPoint_identity]
  exact congrArg (fun f => f.app n (p, PUnit.unit)) (colimitComposition_right_unit W X Y)

end SerrePositivity.EInfinity.Hammock
