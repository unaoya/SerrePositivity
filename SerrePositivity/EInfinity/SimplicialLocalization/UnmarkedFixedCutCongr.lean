module

public import SerrePositivity.EInfinity.SimplicialLocalization.UnmarkedFixedCutSandwich

/-!
# 同じ射列の等式による固定切断の表示変更

概要：射列の等式で切断を移しても、元の接頭射列・残りの射列は変わらない。
方針：射列の等式の帰納と固定切断の一意性を使う。
規約：同じ端点と同じ生成矢を保持する。
使われ方：区間合成の因子化と元の切断の厳密な照合。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.EInfinity.SimplicialLocalization.GeneratorWord.FixedCut
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {a : Quiver.Total C} {X Y : C} {p q : Quiver.Path X Y}

def congr (h : p = q) (P : FixedCut W a p) : FixedCut W a q := h ▸ P

lemma congr_left (h : p = q) (P : FixedCut W a p) : (congr W h P).left = P.left := by
  cases h
  rfl

lemma congr_right (h : p = q) (P : FixedCut W a p) : (congr W h P).right = P.right := by
  cases h
  rfl

variable {X' Y' : C} (P : FixedCut W a p)
  (u : Quiver.Path X' X) (v : Quiver.Path Y Y') (hu : W.paths u)
  {r : Quiver.Path X' Y'} (hr : r = u.comp (p.comp v)) (Q : FixedCut W a r)

include hu hr in
lemma factorization_left : Q.left = u.comp P.left :=
  (congr_left W hr Q).symm.trans
    (congrArg (fun R => R.left) (fixedCut_ext W (congr W hr Q) (sandwich W P u v hu)))

include hu hr in
lemma factorization_right : Q.right = P.right.comp v :=
  (congr_right W hr Q).symm.trans
    (congrArg (fun R => R.right) (fixedCut_ext W (congr W hr Q) (sandwich W P u v hu)))

end SerrePositivity.EInfinity.SimplicialLocalization.GeneratorWord.FixedCut
