module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentSubdivision
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitCompositionPoints
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionArrowComparison
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# 元の二つの forward 射の連結と厳密な合成

概要：元の二列を同じ語の圧縮で元の合成射の一列へ戻す。
方針：全頂点・二つの隣接射・区間合成と一定単体の全縦射を照合する。
規約：元の射と元の全次数の点を保持する。
使われ方：通常圏から hammock への実関手の合成保存。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardPairComposition
open CategoryTheory

abbrev pairWord : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)
def collapse : pairWord ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward where
  orderHom := OrderHom.const _ (0 : Fin 1)
  direction_eq i := by fin_cases i <;> rfl
lemma collapse_cut (j : Fin 2) : collapse.cut j = (![0, 2] : Fin 2 → Fin 3) j := by
  fin_cases j <;> decide
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X Y Z : C}
lemma collapse_obj (f : X ⟶ Y) (g : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj collapse (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) g)) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) (f ≫ g) := by
  let S := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) g)
  have h0 : S.arrow (0 : Fin 2) = f :=
    eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) g) (0 : Fin 1))
  have h1 : S.arrow (1 : Fin 2) = g :=
    eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_right_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) g) (0 : Fin 1))
  have he0 : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S 0 1 (by decide)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.adjacent_direction (w := pairWord) .forward (0 : Fin 2) rfl) = f :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_adjacent .forward S (0 : Fin 2) rfl).trans
      ((eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forward_arrow_heq S (0 : Fin 2) rfl)).trans h0)
  have he1 : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S 1 2 (by decide)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.adjacent_direction (w := pairWord) .forward (1 : Fin 2) rfl) = g :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_adjacent .forward S (1 : Fin 2) rfl).trans
      ((eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forward_arrow_heq S (1 : Fin 2) rfl)).trans h1)
  have hd : ∀ i : Fin 2, 0 ≤ i.val → i.val < 2 → pairWord.direction i = .forward := by
    intro i _ _
    fin_cases i <;> rfl
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S 0 2 (by decide) hd = f ≫ g :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentSubdivision.map_comp .forward S 0 1 2 (by decide) (by decide) hd).trans
      (congrArg₂ (fun a b => a ≫ b) he0 he1)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext
  · intro j
    change S.vertex (collapse.cut j) = _
    rw [collapse_cut]
    fin_cases j <;> rfl
  · intro i
    change Fin 1 at i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact heq_of_eq he
lemma collapse_simplex (f : X ⟶ Y) (g : Y ⟶ Z) (n : SimplexCategoryᵒᵖ) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowSimplex W f n).prod' (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowSimplex W g n) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor) ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor collapse = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowSimplex W (f ≫ g) n := by
  apply CategoryTheory.Functor.ext (F := _)
    (G := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowSimplex W (f ≫ g) n) (fun _ => collapse_obj W f g) ?_
  intro i j θ
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor collapse).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor.map (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) f, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) g))) =
    eqToHom _ ≫ 𝟙 _ ≫ eqToHom _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, eqToHom_trans, eqToHom_refl]

lemma composePoint_arrowPoint (f : X ⟶ Y) (g : Y ⟶ Z) (n : SimplexCategoryᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W X Y Z (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint W f n) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint W g n) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint W (f ≫ g) n := by
  have h := congrArg (fun k => k.app n
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowSimplex W f n).prod' (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowSimplex W g n) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion_naturality W X Z collapse)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_inclusions]
  exact h.symm.trans
    (congrArg (fun σ => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Z (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)).app n σ)
      (collapse_simplex W f g n))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardPairComposition
