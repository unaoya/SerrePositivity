module

public import SerrePositivity.EInfinity.Hammock.ZigzagAppendFunctor
public import SerrePositivity.EInfinity.Hammock.SegmentSubdivision
public import SerrePositivity.EInfinity.Hammock.ColimitCompositionPoints
public import SerrePositivity.EInfinity.Hammock.DirectionArrowComparison
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# 元の二つの forward 射の連結と厳密な合成

概要：元の二列を同じ語の圧縮で元の合成射の一列へ戻す。
方針：全頂点・二つの隣接射・区間合成と一定単体の全縦射を照合する。
規約：元の射と元の全次数の点を保持する。
使われ方：通常圏から hammock への実関手の合成保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Hammock.ForwardPair
open CategoryTheory

abbrev pairWord : Word := Word.append (Word.single .forward) (Word.single .forward)
def collapse : pairWord ⟶ Word.single .forward where
  orderHom := OrderHom.const _ (0 : Fin 1)
  direction_eq i := by fin_cases i <;> rfl
lemma collapse_cut (j : Fin 2) : collapse.cut j = (![0, 2] : Fin 2 → Fin 3) j := by
  fin_cases j <;> decide
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X Y Z : C}
lemma collapse_obj (f : X ⟶ Y) (g : Y ⟶ Z) :
    WordAction.obj collapse (ZigzagAppend.obj (ForwardZigzag.obj (W := W) f)
      (ForwardZigzag.obj (W := W) g)) = ForwardZigzag.obj (W := W) (f ≫ g) := by
  let S := ZigzagAppend.obj (ForwardZigzag.obj (W := W) f) (ForwardZigzag.obj (W := W) g)
  have h0 : S.arrow (0 : Fin 2) = f :=
    eq_of_heq (ZigzagAppend.arrow_left_heq (ForwardZigzag.obj (W := W) f)
      (ForwardZigzag.obj (W := W) g) (0 : Fin 1))
  have h1 : S.arrow (1 : Fin 2) = g :=
    eq_of_heq (ZigzagAppend.arrow_right_heq (ForwardZigzag.obj (W := W) f)
      (ForwardZigzag.obj (W := W) g) (0 : Fin 1))
  have he0 : Segment.map .forward S 0 1 (by decide)
      (Segment.adjacent_direction (w := pairWord) .forward (0 : Fin 2) rfl) = f :=
    (Segment.map_adjacent .forward S (0 : Fin 2) rfl).trans
      ((eq_of_heq (Direction.forward_arrow_heq S (0 : Fin 2) rfl)).trans h0)
  have he1 : Segment.map .forward S 1 2 (by decide)
      (Segment.adjacent_direction (w := pairWord) .forward (1 : Fin 2) rfl) = g :=
    (Segment.map_adjacent .forward S (1 : Fin 2) rfl).trans
      ((eq_of_heq (Direction.forward_arrow_heq S (1 : Fin 2) rfl)).trans h1)
  have hd : ∀ i : Fin 2, 0 ≤ i.val → i.val < 2 → pairWord.direction i = .forward := by
    intro i _ _
    fin_cases i <;> rfl
  have he : Segment.map .forward S 0 2 (by decide) hd = f ≫ g :=
    (Segment.map_comp .forward S 0 1 2 (by decide) (by decide) hd).trans
      (congrArg₂ (fun a b => a ≫ b) he0 he1)
  apply Zigzag.object_ext
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
    ((arrowSimplex W f n).prod' (arrowSimplex W g n) ⋙ ZigzagAppend.functor) ⋙
        WordAction.functor collapse = arrowSimplex W (f ≫ g) n := by
  apply CategoryTheory.Functor.ext (F := _)
    (G := arrowSimplex W (f ≫ g) n) (fun _ => collapse_obj W f g) ?_
  intro i j θ
  change (WordAction.functor collapse).map
      (ZigzagAppend.functor.map (𝟙 (ForwardZigzag.obj (W := W) f, ForwardZigzag.obj (W := W) g))) =
    eqToHom _ ≫ 𝟙 _ ≫ eqToHom _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, eqToHom_trans, eqToHom_refl]

lemma composePoint_arrowPoint (f : X ⟶ Y) (g : Y ⟶ Z) (n : SimplexCategoryᵒᵖ) :
    composePoint W X Y Z (arrowPoint W f n) (arrowPoint W g n) = arrowPoint W (f ≫ g) n := by
  have h := congrArg (fun k => k.app n
    ((arrowSimplex W f n).prod' (arrowSimplex W g n) ⋙ ZigzagAppend.functor))
    (graphInclusion_naturality W X Z collapse)
  rw [arrowPoint, arrowPoint, composePoint_inclusions]
  exact h.symm.trans
    (congrArg (fun σ => (graphInclusion W X Z (Word.single .forward)).app n σ)
      (collapse_simplex W f g n))

end SerrePositivity.EInfinity.Hammock.ForwardPair
