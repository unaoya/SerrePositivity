module

public import SerrePositivity.EInfinity.Hammock.ForwardSegmentColumnFactorization
public import SerrePositivity.EInfinity.Hammock.WordColumnRecovery
public import SerrePositivity.EInfinity.Hammock.DirectionArrowComparison
public import SerrePositivity.EInfinity.SimplicialLocalization.UnmarkedFixedCutHEq

/-!
# 元の語の圧縮した列の切断の前後の射列

概要：同じ fiber の内部一列で切断した元の接頭射・残りを圧縮後に回収する。
方針：元の生の列を挟む因子化と固定切断の一意性を使う。
規約：元の端点移送と全射列を保持し、後置区間の指定性を仮定しない。
使われ方：prefixMap・残りの全語の hammock 余極限への整合。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.WordActionCut
open CategoryTheory SimplicialLocalization.GeneratorWord

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {a b : Word} {X Y : Paths C} (f : a ⟶ b) (S : Zigzag W.paths a X Y)
  (j : Fin b.length) (i : Fin a.length) (hi : f.orderHom i = j) (hj : b.direction j = .forward)

abbrev direction := fun k hk hk' => (f.fiber_direction j k hk hk').trans hj

abbrev bounds := (f.fiber_iff j i).2 hi

def prefixMap : S.vertex (f.cut j.castSucc) ⟶ S.vertex (a.source i) :=
  Segment.toColumn S (f.cut j.castSucc) (f.cut j.succ) (direction f j hj) i
    (bounds f j i hi).1 (bounds f j i hi).2

def residual : S.vertex (a.target i) ⟶ S.vertex (f.cut j.succ) :=
  Segment.fromColumn S (f.cut j.castSucc) (f.cut j.succ) (direction f j hj) i
    (bounds f j i hi).1 (bounds f j i hi).2

lemma factorization : HEq ((WordAction.obj f S).arrow j)
    ((prefixMap W f S j i hi hj).comp ((S.arrow i).comp (residual W f S j i hi hj))) := by
  have hc := (Direction.forward_arrow_heq (WordAction.obj f S) j hj).symm.trans
    (WordAction.arrow_obj_heq f S .forward j hj)
  exact hc.trans (heq_of_eq (Segment.map_column_factorization S
    (f.cut j.castSucc) (f.cut j.succ) (f.cut_monotone (Fin.castSucc_le_succ j))
    (direction f j hj) i (bounds f j i hi).1 (bounds f j i hi).2))

include hj in
lemma source_eq : (WordAction.obj f S).vertex (b.source j) = S.vertex (f.cut j.castSucc) :=
  congrArg (fun k => S.vertex (f.cut k)) (by simp [Word.source, hj])

include hj in
lemma target_eq : (WordAction.obj f S).vertex (b.target j) = S.vertex (f.cut j.succ) :=
  congrArg (fun k => S.vertex (f.cut k)) (by simp [Word.target, hj])

lemma prefix_mem
    (hV : ∀ k : Fin a.length, (f.cut j.castSucc).val ≤ k.val → k.val < i.val →
      W.paths (S.arrow k)) : W.paths (prefixMap W f S j i hi hj) :=
  Segment.toColumn_mem S (f.cut j.castSucc) (f.cut j.succ) (direction f j hj) i
    (bounds f j i hi).1 (bounds f j i hi).2 W.paths hV

variable (hV : ∀ k : Fin a.length, (f.cut j.castSucc).val ≤ k.val → k.val < i.val →
    W.paths (S.arrow k)) {g : Quiver.Total C} (P : FixedCut W g (S.arrow i))
  (Q : FixedCut W g ((WordAction.obj f S).arrow j))

include hV in
lemma cut_left : HEq Q.left ((prefixMap W f S j i hi hj).comp P.left) :=
  FixedCut.left_heq W (source_eq W f S j hj) (target_eq W f S j hj)
    (factorization W f S j i hi hj) Q
    (FixedCut.sandwich W P (prefixMap W f S j i hi hj) (residual W f S j i hi hj)
      (prefix_mem W f S j i hi hj hV))

include hV in
lemma cut_right : HEq Q.right (P.right.comp (residual W f S j i hi hj)) :=
  FixedCut.right_heq W (source_eq W f S j hj) (target_eq W f S j hj)
    (factorization W f S j i hi hj) Q
    (FixedCut.sandwich W P (prefixMap W f S j i hi hj) (residual W f S j i hi hj)
      (prefix_mem W f S j i hi hj hV))

end SerrePositivity.EInfinity.Hammock.WordActionCut
