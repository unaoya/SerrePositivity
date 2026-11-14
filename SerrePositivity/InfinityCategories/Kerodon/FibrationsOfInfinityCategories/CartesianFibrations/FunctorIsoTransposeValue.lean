module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.InternalHomSwapEvaluationRight
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FunctorIsoValueCurry
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.JointComparisonPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexSectionBaseChange

/-!
概要：転置した指定二変数同型の値を元の同じ係数評価として読む。
方針：元の内部Hom交換と評価の合成則を同じ頂点同型へ写す。
規約：元の同型を保持し、別の点ごとの同型を選ばない。
使われ方：Kerodon §5.6（Tag 027M）の共同切断比較の係数計算。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
namespace CartesianFibrations

/-- 概要：指定同型の転置を一係数で評価すると、元の同型の同じ評価後合成になる。
方針：同じ交換射と評価の合成則を、元の頂点同型の像へ送る。
規約：端点移送だけの異種等式。使われ方：指定底変換の係数値を元の比較の因子へ分ける。 -/
lemma functorIsoValue_transpose_heq_postcomp {A I X : SSet.{u}}
    {F G : A ⟶ (ihom I).obj X} (e : FunctorIso F G) (i : I _⦋0⦌) :
    HEq (functorIsoValue e.transpose i) (e.postcomp (evaluateFunctorAt (Y := X) i)) := by
  have h := functorIsoValue_heq_map e.transpose i
  rw [FunctorIso.transpose, vertexIso_map_comp] at h
  have hp : e.postcomp (evaluateFunctorAt (Y := X) i) =
      VertexIso.map e ((ihom A).map (evaluateFunctorAt (Y := X) i)) :=
    Project.QuasicategoryAuxiliaries.functorIso_postcomp_eq_mapIso e _
  exact h.trans ((vertexIso_map_heq e (internalHomSwapIso_evaluate_right A I X i)).trans hp.symm.heq)

end CartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
