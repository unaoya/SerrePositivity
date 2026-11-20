module


public import SerrePositivity.InfinityCategories.Project.PointedSpaces.FramedTetrahedronRelation

/-!
概要：共通の外辺を持つ二つの三単体から、零ホモトピーの差と元の右辺の逆の式を得る。
方針：内辺を恒等に消し、参照三単体の右辺も恒等に消して同じ外辺で比較する。
規約：基点からの経路は右向きの合成、差は参照経路の逆を左から合成する。
使われ方：edgewise 反転比較と元の円評価錐の符号の確認。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.FramedTetrahedron
end SerrePositivity.KST.Spectra.FramedTetrahedron
namespace SerrePositivity.InfinityCategories.Project.PointedSpaces
open _root_.SerrePositivity.KST.Spectra.FramedTetrahedron
variable {X : SSet.{u}} (f g : (Δ[3] : SSet.{u}) ⟶ X) (p x : X _⦋0⦌)
    (hf : ∀ i : Fin 4, f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm i) = _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.vertex p x i)
    (hg : ∀ i : Fin 4, g.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm i) = _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.vertex p x i)
    (hiF : f.app (Opposite.op ⦋1⦌) (stdSimplex.edge 3 1 2 (of_decide_eq_true rfl)) = (X.σ 0) x)
    (hiG : g.app (Opposite.op ⦋1⦌) (stdSimplex.edge 3 1 2 (of_decide_eq_true rfl)) = (X.σ 0) x)
    (hrG : g.app (Opposite.op ⦋1⦌) (stdSimplex.edge 3 2 3 (of_decide_eq_true rfl)) = (X.σ 0) x)
    (ho : f.app (Opposite.op ⦋1⦌) (stdSimplex.edge 3 0 3 (of_decide_eq_true rfl)) =
      g.app (Opposite.op ⦋1⦌) (stdSimplex.edge 3 0 3 (of_decide_eq_true rfl)))

include hiF hiG hrG ho

/-- 二つの内辺と参照の右辺が定値なら、元の左辺と右辺の合成は参照の左辺。 -/
lemma comparison :
    SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.edge f p x hf 0 1 (of_decide_eq_true rfl)) ≫
        SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.edge f p x hf 2 3 (of_decide_eq_true rfl)) =
      SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.edge g p x hg 0 1 (of_decide_eq_true rfl)) := by
  have hF := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.left_comp_right f p x hf hiF
  have hG := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.left_comp_right g p x hg hiG
  have hr : _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.edge g p x hg 2 3 (of_decide_eq_true rfl) = SSet.Edge.id x := SSet.Edge.ext hrG
  have houter : _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.edge f p x hf 0 3 (of_decide_eq_true rfl) =
      _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.edge g p x hg 0 3 (of_decide_eq_true rfl) :=
    SSet.Edge.ext ho
  erw [hr, SSet.HomotopyCategory.homMk_id, Category.comp_id] at hG
  exact hF.trans ((congrArg SSet.HomotopyCategory.homMk houter).trans hG.symm)

/-- 参照経路に対する差は、元の右辺の逆の類である。 -/
lemma difference_inverse
    [IsIso (SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.edge g p x hg 0 1 (of_decide_eq_true rfl)))]
    [IsIso (SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.edge f p x hf 2 3 (of_decide_eq_true rfl)))] :
    inv (SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.edge g p x hg 0 1 (of_decide_eq_true rfl))) ≫
        SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.edge f p x hf 0 1 (of_decide_eq_true rfl)) =
      inv (SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.edge f p x hf 2 3 (of_decide_eq_true rfl))) := by
  apply (cancel_mono (SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.edge f p x hf 2 3 (of_decide_eq_true rfl)))).mp
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.comparison f g p x hf hg hiF hiG hrG ho, IsIso.inv_hom_id]

end SerrePositivity.InfinityCategories.Project.PointedSpaces

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
