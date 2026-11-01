module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ForwardTripleSegment
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordIdentity
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ForwardZigzag

/-!
# 元の三列 collapse による同じ合成射の回収

概要：元の WordAction の三列圧縮を、同じ三射の合成と照合する。
方針：両端の cut を異種等式で移し、元の区間合成を回収する。
規約：頂点の表示の移送を含め、元の語の射と元の列を使う。
使われ方：内部切断の三射の因子化を元の全図式へ戻す。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ForwardTriple
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {X Y : C}
  (S : Zigzag W Word.ForwardTriple.word X Y)

lemma column_heq :
    HEq (WordAction.column Word.ForwardTriple.collapse S (0 : Fin 1))
      (Direction.arrow .forward S (0 : Fin 3) (Word.ForwardTriple.direction 0) ≫
        Direction.arrow .forward S (1 : Fin 3) (Word.ForwardTriple.direction 1) ≫
          Direction.arrow .forward S (2 : Fin 3) (Word.ForwardTriple.direction 2)) := by
  have h := WordAction.segment_heq_of_eq .forward S
    Word.ForwardTriple.cut_zero Word.ForwardTriple.cut_last
    (Word.ForwardTriple.collapse.cut_monotone (Fin.castSucc_le_succ (0 : Fin 1)))
    (by decide) (fun i hi hi' => Word.ForwardTriple.collapse.fiber_direction (0 : Fin 1) i hi hi')
    (fun i _ _ => Word.ForwardTriple.direction i)
  exact h.trans (heq_of_eq (segment_composite S))

/-- 元の端点表示に移した同じ三射の合成。 -/
def composite : X ⟶ Y :=
  eqToHom S.first.symm ≫
    Direction.arrow .forward S (0 : Fin 3) (Word.ForwardTriple.direction 0) ≫
      Direction.arrow .forward S (1 : Fin 3) (Word.ForwardTriple.direction 1) ≫
        Direction.arrow .forward S (2 : Fin 3) (Word.ForwardTriple.direction 2) ≫
          eqToHom S.last

lemma obj_eq [W.IsMultiplicative] :
    WordAction.obj Word.ForwardTriple.collapse S = ForwardZigzag.obj (composite S) := by
  apply Zigzag.object_ext
  · intro i
    change Fin 2 at i
    cases i using Fin.cases with
    | zero => exact (congrArg S.vertex Word.ForwardTriple.cut_zero).trans S.first
    | succ i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact (congrArg S.vertex Word.ForwardTriple.cut_last).trans S.last
  · intro i
    change Fin 1 at i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    change HEq (WordAction.column Word.ForwardTriple.collapse S (0 : Fin 1))
      (composite S)
    dsimp only [composite]
    simp only [heq_eqToHom_comp_iff]
    simp only [← Category.assoc, heq_comp_eqToHom_iff]
    simpa only [Category.assoc] using column_heq S

end SerrePositivity.EInfinity.Hammock.ForwardTriple
