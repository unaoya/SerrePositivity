module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FunctorIsoTransposeValue

/-!
概要：転置後の指定同型の係数評価を、転置前の同じ対象成分へ戻す。
方針：内部Hom交換と第一変数評価の既存の合成則を使う。
規約：元の同型を保持する。
使われ方：Kerodon §5.1（Tag 01T1）の共同切断比較の係数計算。
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

/-- 概要：指定同型の転置の元の第一変数での係数評価は、元の同じ対象成分。
方針：内部Hom交換と第一変数評価の合成則を元の同型へ写す。
規約：元の同型を保持する。使われ方：共同切断比較の係数移送。 -/
lemma functorIso_transpose_postcomp_heq_value {A I X : SSet.{u}}
    {F G : A ⟶ (ihom I).obj X} (e : FunctorIso F G) (a : A _⦋0⦌) :
    HEq (FunctorIso.postcomp e.transpose (evaluateFunctorAt (Y := X) a))
      (functorIsoValue e a) := by
  have hp : FunctorIso.postcomp e.transpose (evaluateFunctorAt (Y := X) a) =
      VertexIso.map e.transpose ((ihom I).map (evaluateFunctorAt (Y := X) a)) :=
    Project.QuasicategoryAuxiliaries.functorIso_postcomp_eq_mapIso e.transpose _
  apply HEq.trans hp.heq
  change HEq (VertexIso.map (VertexIso.map e (internalHomSwapIso A I X).hom)
    ((ihom I).map (evaluateFunctorAt (Y := X) a))) (functorIsoValue e a)
  rw [vertexIso_map_comp]
  exact (vertexIso_map_heq e (internalHomSwapIso_evaluate A I X a)).trans
    (functorIsoValue_heq_map e a).symm

end CartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
