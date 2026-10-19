module

public import SerrePositivity.InfinityCategories.F2.CatTriangleIso

/-!
概要：Cat_∞ の三辺が指定関手である三角形の可換性。
方針：三頂点と三辺の射データを揃えて元の三角形の関手同型を移す。
規約：長辺から二辺の合成への向きを保持する。
使われ方：引き戻し錐の二つの native な三角形の可換性の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：三辺を指定関手と同定した Cat_∞ の三角形から指定関手同型を作る。
方針：三つの対象と射を元の辺から同時に読み戻し、三角形の同型を輸送する。
規約：元の二単体を変更せず、別の関手同型の代表を選ばない。
使われ方：native な錐の三角形を二脚と図式の射の関手同型にする。 -/
def catInfinityTriangleIso_of_faces {X Y Z : QCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (s : CatInfinity.{u} _⦋2⦌)
    (h₂ : CatInfinity.δ 2 s = (coherentNerveEdge f).edge)
    (h₀ : CatInfinity.δ 0 s = (coherentNerveEdge g).edge)
    (h₁ : CatInfinity.δ 1 s = (coherentNerveEdge h).edge) : FunctorIso h (f ≫ g) := by
  have hx : s.obj ⟨ULift.up 0⟩ = X :=
    congrArg (fun t : CatInfinity.{u} _⦋1⦌ ↦ t.obj ⟨ULift.up 0⟩) h₂
  have hy : s.obj ⟨ULift.up 1⟩ = Y :=
    congrArg (fun t : CatInfinity.{u} _⦋1⦌ ↦ t.obj ⟨ULift.up 1⟩) h₂
  have hz : s.obj ⟨ULift.up 2⟩ = Z :=
    congrArg (fun t : CatInfinity.{u} _⦋1⦌ ↦ t.obj ⟨ULift.up 1⟩) h₀
  subst X
  subst Y
  subst Z
  have hf : coherentEdgeHom (CatInfinity.δ 2 s) = f := by
    have h := congrArg coherentNerveArrowData h₂
    rw [coherentNerveEdge_edge, coherentNerveArrowData_of_arrow] at h
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
  have hg : coherentEdgeHom (CatInfinity.δ 0 s) = g := by
    have h := congrArg coherentNerveArrowData h₀
    rw [coherentNerveEdge_edge, coherentNerveArrowData_of_arrow] at h
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
  have hh : coherentEdgeHom (CatInfinity.δ 1 s) = h := by
    have he := congrArg coherentNerveArrowData h₁
    rw [coherentNerveEdge_edge, coherentNerveArrowData_of_arrow] at he
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj he).2)).2
  have e := catInfinityTriangleIso s
  rw [hf, hg, hh] at e
  exact e

end SerrePositivity.InfinityCategories.F2
