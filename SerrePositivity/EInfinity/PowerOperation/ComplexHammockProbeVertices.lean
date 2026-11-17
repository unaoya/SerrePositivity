module

public import SerrePositivity.EInfinity.PowerOperation.ComplexHammockProbeFunctor

/-!
# 同じ hammock の probe 自己同値の全頂点での値

DAG XIII §2.2 の指定比較の充満忠実性を全頂点へ延ばすための照合。
元の通常対象と元の局所化源の零単体を保つ。［一般∞］移動候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
open ClassificationOfCocartesianFibrations (coherentNerveMap_vertex)
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open TheSliceAndJoinConstructions (nerveVertex)
open scoped Simplicial
variable (A : Type u) [CommRing A]

def complexHammockOriginalObject (x : (complexHammockNerve A) _⦋0⦌) : Complex A :=
  (complexRelativeDown A).obj (coherentNerveObject (C := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockCategory
    (complexRelativeCategory A)) x)

lemma complexHammockProbe_vertex (x : (complexHammockNerve A) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockNerve (complexRelativeProbeMorphism A)).app (Opposite.op ⦋0⦌) x =
      (complexHammockSource A).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ ((complexRelativeUp A).obj
          ((framedLimitProbeFunctor A).obj (complexHammockOriginalObject A x)))) := by
  let Z := coherentNerveObject (C := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockCategory (complexRelativeCategory A)) x
  have hx : coherentNerveVertex Z = x := coherentNerveVertex_object x
  have h₀ := congrArg
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockNerve (complexRelativeProbeMorphism A)).app (Opposite.op ⦋0⦌)) hx.symm
  have h₁ := coherentNerveMap_vertex (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockFunctor (complexRelativeProbeMorphism A)) Z
  have h₂ := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap_vertex (complexRelativeCategory A)
    ((complexRelativeProbeMorphism A).functor.obj Z)
  have hz : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockFunctor (complexRelativeProbeMorphism A)).obj Z =
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor (complexRelativeCategory A)).obj
        ((complexRelativeProbeMorphism A).functor.obj Z) := rfl
  have h := h₀.trans (h₁.trans ((congrArg coherentNerveVertex hz).trans h₂.symm))
  dsimp only [complexRelativeProbeMorphism, complexHammockOriginalObject, Z] at h ⊢
  exact h

end SerrePositivity.EInfinity.PowerOperation
