module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatTriangleConstantIso
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoWhiskerAlgebra

/-!
概要：境界関手を指定した定値三角形の同型の簡約。
方針：頂点と境界の等式を消去して元の三角形へ戻す。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：三辺を指定しても定値三角形の同型は等式から来る。
方針：頂点と境界関手の等式を消去して元の三角形に戻す。
規約：指定された値を保持する。
使われ方：strict な比較三角形の同型の簡約。 -/
lemma isFunctorEqIso_catInfinityTriangleIso_of_faces {X Y Z : QCat.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (s : CatInfinity.{u} _⦋2⦌)
    (h₂ : CatInfinity.δ 2 s = (coherentNerveEdge f).edge)
    (h₀ : CatInfinity.δ 0 s = (coherentNerveEdge g).edge)
    (h₁ : CatInfinity.δ 1 s = (coherentNerveEdge h).edge)
    (hs : IsConstantCoherentTriangle s) :
    IsFunctorEqIso (catInfinityTriangleIso_of_faces f g h s h₂ h₀ h₁) := by
  have hx : s.obj ⟨ULift.up 0⟩ = X :=
    congrArg (fun t : CatInfinity.{u} _⦋1⦌ ↦ t.obj ⟨ULift.up 0⟩) h₂
  have hy : s.obj ⟨ULift.up 1⟩ = Y :=
    congrArg (fun t : CatInfinity.{u} _⦋1⦌ ↦ t.obj ⟨ULift.up 1⟩) h₂
  have hz : s.obj ⟨ULift.up 2⟩ = Z :=
    congrArg (fun t : CatInfinity.{u} _⦋1⦌ ↦ t.obj ⟨ULift.up 1⟩) h₀
  subst X
  subst Y
  subst Z
  have hf : coherentEdgeHom (CatInfinity.δ 2 s) = f :=
    eq_of_heq (coherentEdgeHom_of_edge_eq h₂)
  have hg : coherentEdgeHom (CatInfinity.δ 0 s) = g :=
    eq_of_heq (coherentEdgeHom_of_edge_eq h₀)
  have hh : coherentEdgeHom (CatInfinity.δ 1 s) = h :=
    eq_of_heq (coherentEdgeHom_of_edge_eq h₁)
  subst f
  subst g
  subst h
  change IsFunctorEqIso (catInfinityTriangleIso s)
  exact isFunctorEqIso_catInfinityTriangleIso s hs

end SerrePositivity.InfinityCategories.F2
