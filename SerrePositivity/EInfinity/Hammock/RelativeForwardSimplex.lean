module

public import SerrePositivity.EInfinity.Hammock.RelativeCompositionPoints
public import SerrePositivity.EInfinity.Hammock.ColimitIdentityPoint

/-!
# 元の相対関手による一列の点と単位点の保存

概要：元の任意の射の一定単体と元の単位点を同じ余極限写像で回収する。
方針：二頂点・一列・全縦成分と元の標準射を照合する。
規約：恒等文字への置換をせず元の射を関手で送る。
使われ方：指定部分圏の包含の単位保存。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Zigzag.Relative
open CategoryTheory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  (F : LocalizerMorphism W V) {X Y : C}

omit [W.IsMultiplicative] [V.IsMultiplicative] in
lemma forward_obj (p : X ⟶ Y) :
    obj F (ForwardZigzag.obj (W := W) p) = ForwardZigzag.obj (W := V) (F.functor.map p) := by
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
    rfl

lemma arrowSimplex_map (p : X ⟶ Y) (n : SimplexCategoryᵒᵖ) :
    arrowSimplex W p n ⋙ functor F = arrowSimplex V (F.functor.map p) n := by
  apply CategoryTheory.Functor.hext (fun _ => forward_obj F p)
  intro d e f
  apply Zigzag.hom_hext (forward_obj F p) (forward_obj F p)
  intro j
  change Fin 2 at j
  cases j using Fin.cases with
  | zero => exact heq_of_eq (F.functor.map_id _)
  | succ j => exact heq_of_eq (F.functor.map_id _)

end SerrePositivity.EInfinity.Hammock.Zigzag.Relative
namespace SerrePositivity.EInfinity.Hammock.Relative
open CategoryTheory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  (F : LocalizerMorphism W V) {X Y : C}

lemma arrowPoint_map (p : X ⟶ Y) (n : SimplexCategoryᵒᵖ) :
    (colimitMap F X Y).app n (arrowPoint W p n) = arrowPoint V (F.functor.map p) n :=
  (graphInclusion_point F (arrowSimplex W p n)).trans
    (congrArg (fun H => (graphInclusion V (F.functor.obj X) (F.functor.obj Y)
      (Word.single .forward)).app n H) (Zigzag.Relative.arrowSimplex_map F p n))

lemma colimitUnit_point (X : C) (n : SimplexCategoryᵒᵖ) :
    (colimitMap F X X).app n ((colimitUnit W X).app n PUnit.unit) =
      (colimitUnit V (F.functor.obj X)).app n PUnit.unit := by
  rw [← arrowPoint_identity, arrowPoint_map, F.functor.map_id, arrowPoint_identity]

end SerrePositivity.EInfinity.Hammock.Relative
