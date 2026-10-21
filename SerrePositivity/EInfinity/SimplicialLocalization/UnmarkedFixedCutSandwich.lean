module

public import SerrePositivity.EInfinity.SimplicialLocalization.UnmarkedFixedCut

/-!
# 固定生成矢での切断の前後への連結と厳密な回収

概要：指定前置射列と任意の後置射列を加えた元の固定切断を構成する。
方針：元の射列の結合則と固定切断の一意性を使う。
規約：同じ元の生成矢と前後の射列を保持する。
使われ方：圧縮後の切断の接頭射・残りを元の切断へ照合する。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.EInfinity.SimplicialLocalization.GeneratorWord.FixedCut
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {a : Quiver.Total C} {X Y X' Y' : C} {p : Quiver.Path X Y} (P : FixedCut W a p)
  (u : Quiver.Path X' X) (v : Quiver.Path Y Y') (hu : W.paths u)

def sandwich : FixedCut W a (u.comp (p.comp v)) where
  left := u.comp P.left
  right := P.right.comp v
  left_mem := W.paths.comp_mem _ _ hu P.left_mem
  unmarked := P.unmarked
  factorization := (congrArg (fun q : Quiver.Path X Y => u.comp (q.comp v))
    P.factorization).trans (by simp only [Quiver.Path.comp_assoc])

include hu in
lemma sandwich_left (Q : FixedCut W a (u.comp (p.comp v))) : Q.left = u.comp P.left :=
  congrArg (fun R => R.left) (fixedCut_ext W Q (sandwich W P u v hu))

include hu in
lemma sandwich_right (Q : FixedCut W a (u.comp (p.comp v))) : Q.right = P.right.comp v :=
  congrArg (fun R => R.right) (fixedCut_ext W Q (sandwich W P u v hu))

end SerrePositivity.EInfinity.SimplicialLocalization.GeneratorWord.FixedCut
