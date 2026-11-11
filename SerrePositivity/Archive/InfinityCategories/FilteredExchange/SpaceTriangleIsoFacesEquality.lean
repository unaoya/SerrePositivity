module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceTriangleIsoFaces
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentEdgeHomEquality

/-!
概要：三角形の指定同型の端点の輸送による保持。
方針：端点と境界射の等式を消去して指定データを比較する。
規約：単に別の同型の存在を示すのでなく元の値を保持する。
使われ方：四面の合成則を任意に指定した境界関手へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：同じ三角形から得る指定関手同型は型を含めて等しい。
方針：二単体の等式を消去する。
規約：三つの頂点の型が異なる表示を許す。
使われ方：円柱の共有面と側面の同型を一致させる。 -/
lemma spaceInfinityTriangleIso_heq {s t : SpaceInfinity.{u} _⦋2⦌} (h : s = t) :
    HEq (spaceInfinityTriangleIso s) (spaceInfinityTriangleIso t) := by
  cases h
  rfl

/-- 概要：三辺を指定関手で表した同型は元の三角形の同型と型を含めて等しい。
方針：端点と読み戻しの等式を消去する。
規約：対象の等式による型の変化を許す。
使われ方：三角形・四面の同型を共通の境界へ揃える。 -/
lemma spaceInfinityTriangleIso_of_faces_heq {X Y Z : KanObject.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (s : SpaceInfinity.{u} _⦋2⦌)
    (h₂ : SpaceInfinity.δ 2 s = (coherentNerveEdge f).edge)
    (h₀ : SpaceInfinity.δ 0 s = (coherentNerveEdge g).edge)
    (h₁ : SpaceInfinity.δ 1 s = (coherentNerveEdge h).edge) :
    HEq (spaceInfinityTriangleIso_of_faces f g h s h₂ h₀ h₁) (spaceInfinityTriangleIso s) := by
  have hx : s.obj ⟨ULift.up 0⟩ = X :=
    congrArg (fun t : SpaceInfinity.{u} _⦋1⦌ ↦ t.obj ⟨ULift.up 0⟩) h₂
  have hy : s.obj ⟨ULift.up 1⟩ = Y :=
    congrArg (fun t : SpaceInfinity.{u} _⦋1⦌ ↦ t.obj ⟨ULift.up 1⟩) h₂
  have hz : s.obj ⟨ULift.up 2⟩ = Z :=
    congrArg (fun t : SpaceInfinity.{u} _⦋1⦌ ↦ t.obj ⟨ULift.up 1⟩) h₀
  subst X
  subst Y
  subst Z
  have hf : coherentEdgeHom (SpaceInfinity.δ 2 s) = f :=
    eq_of_heq (coherentEdgeHom_of_edge_eq h₂)
  have hg : coherentEdgeHom (SpaceInfinity.δ 0 s) = g :=
    eq_of_heq (coherentEdgeHom_of_edge_eq h₀)
  have hh : coherentEdgeHom (SpaceInfinity.δ 1 s) = h :=
    eq_of_heq (coherentEdgeHom_of_edge_eq h₁)
  subst f
  subst g
  subst h
  rfl

end SerrePositivity.InfinityCategories.F2
