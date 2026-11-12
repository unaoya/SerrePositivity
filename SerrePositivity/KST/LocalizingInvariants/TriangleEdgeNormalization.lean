module

public import SerrePositivity.KST.LocalizingInvariants.TriangleEdgeHomotopy

/-!
概要：三角形の二つの辺比較を、指定された元の辺を端点に持つホモトピーにする。
方針：Yoneda の面の式で端点を同定し、全射は同じ退化四角形のまま保持する。
規約：元の二単体と端点を保持。使われ方：BF 区間との全 h Fun 合成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.TriangleEdge

variable {X : SSet.{u}} (s : X _⦋2⦌)

lemma face_map {i : Fin 3} {e : X _⦋1⦌} (h : X.δ i s = e) :
    stdSimplex.δ i ≫ SSet.yonedaEquiv.symm s = SSet.yonedaEquiv.symm e := by
  apply SSet.yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h

def normalizedPost (e d : X _⦋1⦌) (h₂ : X.δ 2 s = e) (h₁ : X.δ 1 s = d) :
    SSet.Homotopy (SSet.yonedaEquiv.symm e) (SSet.yonedaEquiv.symm d) where
  h := SquareDiagonal.postShape ≫ SSet.yonedaEquiv.symm s
  h₀ := by rw [← Category.assoc, SquareDiagonal.postShape_zero, face_map s h₂]; rfl
  h₁ := by rw [← Category.assoc, SquareDiagonal.postShape_one, face_map s h₁]; rfl
  rel := (post (SSet.yonedaEquiv.symm s)).rel

def normalizedPre (d f : X _⦋1⦌) (h₁ : X.δ 1 s = d) (h₀ : X.δ 0 s = f) :
    SSet.Homotopy (SSet.yonedaEquiv.symm d) (SSet.yonedaEquiv.symm f) where
  h := SquareDiagonal.preShape ≫ SSet.yonedaEquiv.symm s
  h₀ := by rw [← Category.assoc, SquareDiagonal.preShape_zero, face_map s h₁]; rfl
  h₁ := by rw [← Category.assoc, SquareDiagonal.preShape_one, face_map s h₀]; rfl
  rel := (pre (SSet.yonedaEquiv.symm s)).rel

lemma normalizedPost_arrow (e d : X _⦋1⦌) (h₂ : X.δ 2 s = e) (h₁ : X.δ 1 s = d) :
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (post (SSet.yonedaEquiv.symm s)))) =
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (normalizedPost s e d h₂ h₁))) :=
  HomotopyArrow.congr _ _ rfl

lemma normalizedPre_arrow (d f : X _⦋1⦌) (h₁ : X.δ 1 s = d) (h₀ : X.δ 0 s = f) :
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (pre (SSet.yonedaEquiv.symm s)))) =
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (normalizedPre s d f h₁ h₀))) :=
  HomotopyArrow.congr _ _ rfl

end SerrePositivity.KST.LocalizingInvariants.TriangleEdge
