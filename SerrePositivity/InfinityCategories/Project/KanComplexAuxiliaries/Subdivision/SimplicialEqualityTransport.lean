module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-! # 単体集合の表示等号に沿う全単体と面の移送
概要：単体集合の表示等号で全単体を移し、元の依存等号と面の実等号を保持する。
方針：表示等号の射と自然性を使い、各単体の依存等号を通常の等号に直す。
規約：単体や辺を選び直さず、元の全高次単体の像そのものを使う。
使われ方：元の四面体の二単体を同じ実 BF 写像空間へ束ねる。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 単体集合の表示を移した全単体は、元の単体と依存等号で一致する。 -/
lemma simplicialEqualityTransport_app_heq {E D : SSet.{u}} (e : E = D) (n : ℕ)
    (x : E _⦋n⦌) : HEq ((eqToHom e).app (Opposite.op ⦋n⦌) x) x := by
  cases e
  rfl

/-- 表示移送後は、指定した全単体への依存等号を通常の等号として回収する。 -/
lemma simplicialEqualityTransport_app_of_heq {E D : SSet.{u}} (e : E = D) (n : ℕ)
    (x : E _⦋n⦌) (y : D _⦋n⦌) (h : HEq x y) :
    (eqToHom e).app (Opposite.op ⦋n⦌) x = y :=
  eq_of_heq ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplicialEqualityTransport_app_heq e n x).trans h)

/-- 全単体の表示移送は、その全ての面と厳密に可換。 -/
lemma simplicialEqualityTransport_face {E D : SSet.{u}} (e : E = D) {n : ℕ}
    (i : Fin (n + 2)) (x : E _⦋n + 1⦌) :
    D.δ i ((eqToHom e).app (Opposite.op ⦋n + 1⦌) x) =
      (eqToHom e).app (Opposite.op ⦋n⦌) (E.δ i x) :=
  (NatTrans.naturality_apply (eqToHom e) (SimplexCategory.δ i).op x).symm

/-- 元の面の全単体を依存等号で指定すれば、移送後の全単体の面を厳密に回収する。 -/
lemma simplicialEqualityTransport_face_of_heq {E D : SSet.{u}} (e : E = D) {n : ℕ}
    (i : Fin (n + 2)) (x : E _⦋n + 1⦌) (y : D _⦋n⦌) (h : HEq (E.δ i x) y) :
    D.δ i ((eqToHom e).app (Opposite.op ⦋n + 1⦌) x) = y :=
  (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplicialEqualityTransport_face e i x).trans
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplicialEqualityTransport_app_of_heq e n _ y h)

/-- 元の二単体が共有する面は、同じ表示移送後にも全体として共有される。 -/
lemma simplicialEqualityTransport_common_face {E D : SSet.{u}} (e : E = D) {n : ℕ}
    (i : Fin (n + 2)) (x y : E _⦋n + 1⦌) (h : E.δ i x = E.δ i y) :
    D.δ i ((eqToHom e).app (Opposite.op ⦋n + 1⦌) x) =
      D.δ i ((eqToHom e).app (Opposite.op ⦋n + 1⦌) y) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplicialEqualityTransport_face, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplicialEqualityTransport_face, h]

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
