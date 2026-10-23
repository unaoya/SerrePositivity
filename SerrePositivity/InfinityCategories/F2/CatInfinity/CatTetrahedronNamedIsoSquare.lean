module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatTriangleFacesEquality
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatTetrahedronIsoSquare

/-!
概要：任意に指定した六境界関手に対する四面の指定同型の合成則。
方針：指定された単体の境界と既存の合成則を使う。
規約：辺と同型の値を新しく選択しない。
使われ方：全錐の比較円柱の三つの合成関係の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：指定した境界射と四面の同型の四面体の合成則。
方針：四頂点と六射を回収し、元の四面の合成則へ戻す。
規約：四つの同型が元の四面の値を保持することを明示する。
使われ方：各比較三単体の合成則を同じ脚と対角関手の間で記述する。 -/
lemma catInfinityTetrahedronIso_square_of_edges {A B C D : QCat.{u}}
    (f01 : A ⟶ B) (f12 : B ⟶ C) (f23 : C ⟶ D)
    (f02 : A ⟶ C) (f13 : B ⟶ D) (f03 : A ⟶ D) (s : CatInfinity.{u} _⦋3⦌)
    (h01 : CatInfinity.δ 2 (CatInfinity.δ 2 s) = (coherentNerveEdge f01).edge)
    (h12 : CatInfinity.δ 2 (CatInfinity.δ 0 s) = (coherentNerveEdge f12).edge)
    (h23 : CatInfinity.δ 0 (CatInfinity.δ 0 s) = (coherentNerveEdge f23).edge)
    (h02 : CatInfinity.δ 1 (CatInfinity.δ 3 s) = (coherentNerveEdge f02).edge)
    (h13 : CatInfinity.δ 1 (CatInfinity.δ 0 s) = (coherentNerveEdge f13).edge)
    (h03 : CatInfinity.δ 1 (CatInfinity.δ 2 s) = (coherentNerveEdge f03).edge)
    (e013 : FunctorIso f03 (f01 ≫ f13)) (e123 : FunctorIso f13 (f12 ≫ f23))
    (e023 : FunctorIso f03 (f02 ≫ f23)) (e012 : FunctorIso f02 (f01 ≫ f12))
    (he013 : HEq e013 (catInfinityTriangleIso (CatInfinity.δ 2 s)))
    (he123 : HEq e123 (catInfinityTriangleIso (CatInfinity.δ 0 s)))
    (he023 : HEq e023 (catInfinityTriangleIso (CatInfinity.δ 1 s)))
    (he012 : HEq e012 (catInfinityTriangleIso (CatInfinity.δ 3 s))) :
    e013 ≪≫ e123.precomp (show A.obj ⟶ B.obj from f01) = e023 ≪≫ e012.postcomp f23 := by
  have ha : s.obj ⟨ULift.up 0⟩ = A :=
    congrArg (fun t : CatInfinity.{u} _⦋1⦌ ↦ t.obj ⟨ULift.up 0⟩) h01
  have hb : s.obj ⟨ULift.up 1⟩ = B :=
    congrArg (fun t : CatInfinity.{u} _⦋1⦌ ↦ t.obj ⟨ULift.up 1⟩) h01
  have hc : s.obj ⟨ULift.up 2⟩ = C :=
    congrArg (fun t : CatInfinity.{u} _⦋1⦌ ↦ t.obj ⟨ULift.up 1⟩) h12
  have hd : s.obj ⟨ULift.up 3⟩ = D :=
    congrArg (fun t : CatInfinity.{u} _⦋1⦌ ↦ t.obj ⟨ULift.up 1⟩) h23
  subst A
  subst B
  subst C
  subst D
  have hf01 : catInfinityTetrahedron01 s = f01 := eq_of_heq (coherentEdgeHom_of_edge_eq h01)
  have hf12 : catInfinityTetrahedron12 s = f12 := eq_of_heq (coherentEdgeHom_of_edge_eq h12)
  have hf23 : catInfinityTetrahedron23 s = f23 := eq_of_heq (coherentEdgeHom_of_edge_eq h23)
  have hf02 : catInfinityTetrahedron02 s = f02 := eq_of_heq (coherentEdgeHom_of_edge_eq h02)
  have hf13 : catInfinityTetrahedron13 s = f13 := eq_of_heq (coherentEdgeHom_of_edge_eq h13)
  have hf03 : catInfinityTetrahedron03 s = f03 := eq_of_heq (coherentEdgeHom_of_edge_eq h03)
  subst f01
  subst f12
  subst f23
  subst f02
  subst f13
  subst f03
  have ht013 : HEq (catInfinityTetrahedronIso013 s)
      (catInfinityTriangleIso (CatInfinity.δ 2 s)) := functorIsoOfEq_heq _ _ _
  have ht023 : HEq (catInfinityTetrahedronIso023 s)
      (catInfinityTriangleIso (CatInfinity.δ 1 s)) := functorIsoOfEq_heq _ _ _
  have ht012 : HEq (catInfinityTetrahedronIso012 s)
      (catInfinityTriangleIso (CatInfinity.δ 3 s)) := functorIsoOfEq_heq _ _ _
  have h013 : e013 = catInfinityTetrahedronIso013 s := eq_of_heq (he013.trans ht013.symm)
  have h023 : e023 = catInfinityTetrahedronIso023 s := eq_of_heq (he023.trans ht023.symm)
  have h012 : e012 = catInfinityTetrahedronIso012 s := eq_of_heq (he012.trans ht012.symm)
  have h123 : e123 = catInfinityTriangleIso (CatInfinity.δ 0 s) := eq_of_heq he123
  subst e013
  subst e023
  subst e012
  subst e123
  exact catInfinityTetrahedronIso_square s

end SerrePositivity.InfinityCategories.F2
