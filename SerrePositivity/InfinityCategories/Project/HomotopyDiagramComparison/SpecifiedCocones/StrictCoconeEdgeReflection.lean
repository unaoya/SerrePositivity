module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.StrictCoconeShapeRestriction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.StrictCoconeLegTriangleShape

/-!
概要：通常の余錐の添字の反転を、指定した辺の全写像で照合する。
方針：標準区間で評価し、反転した二対象の射列を比較する。
規約：辺の向きを逆にし、同じ指定射の op を取る。
使われ方：HTT 4.2.4.1、Kerodon §4.6.7（Tag 01LA）、S8 の元の三角形の係数。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 指定した通常の辺を反転した添字で読むと、同じ反対の射の辺になる。
HTT 4.2.4.1、Kerodon §4.6.7（Tag 01LA）、添字同型の評価の法則。 -/
lemma strictCoconeIndexIso_edge {I : Type u} [SmallCategory I]
    {i j : I} (f : i ⟶ j) :
    (SSet.yonedaEquiv.symm (ULift.up (ComposableArrows.mk₁ f)) :
        (Δ[1] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj (nerve I)) ≫
        (strictCoconeIndexIso.{u, v} I).hom =
      (stdSimplex.opIso ⦋1⦌).inv ≫ SSet.opFunctor.map
        (SSet.yonedaEquiv.symm (ULift.up (ComposableArrows.mk₁ f.op)) :
          (Δ[1] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj (nerve Iᵒᵖ)) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.opObjEquiv.injective
  apply ULift.ext
  refine CategoryTheory.Functor.hext ?_ ?_
  · intro k
    fin_cases k <;> rfl
  · intro k l g
    fin_cases k <;> fin_cases l
    all_goals first
    | rfl
    | have h := leOfHom g
      norm_num at h

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
