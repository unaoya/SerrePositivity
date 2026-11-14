module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreeComputedColimitFamily
import all SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreeColimitFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeRestrictionCartesianEdge
import all SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeRestrictionCartesianEdge
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation

/-!
概要：同じ計算済み全余錐族のapexと、指定された普遍余錐族のapexを比較する。
方針：全族の同型をapex評価へ送り、curryの評価則で元の共同評価と照合する。
規約：点ごとの同型を選び直さず、全パラメーターを同時に扱う。
使われ方：3b-3 R6 U40、実現と指定余極限の全族比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]

/-- U40の前提計算：余錐族のapex評価は共同評価の同じ右端への制限。 -/
lemma coconeFamily_apex_evaluation {P I D : SSet.{u + 1}}
    (f : P ⟶ (ihom (join I (Δ[0] : SSet.{u + 1}))).obj D) :
    f ≫ coconeApexEvaluation I D =
      lift (𝟙 P) (SSet.stdSimplex.isTerminalObj₀.from P) ≫
        (P ◁ joinInr I Δ[0]) ≫ (β_ P (join I Δ[0])).hom ≫ uncurry f := by
  conv_lhs => rw [← curry_uncurry f]
  rw [coconeApexEvaluation,
    SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex]
  rw [lift_whiskerLeft_assoc, lift_braiding_hom_assoc]
  have ht : SSet.stdSimplex.isTerminalObj₀.from P =
      SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [ht, SSet.const_comp]

/-- 同じ計算済み全余錐族のapexの全関手。 -/
def strictSemifreeComputedApexFamily :
    nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A :=
  lift (𝟙 _) (SSet.stdSimplex.isTerminalObj₀.from _) ≫
    (nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ) ◁
      joinInr ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ)) Δ[0]) ≫
        strictSemifreeComputedDAJoinFamily A

private lemma specifiedNativeApex_eq_aux :
    strictSemifreeNativeApexFamily A SimplexCategoryᵒᵖ =
      lift (𝟙 _) (SSet.stdSimplex.isTerminalObj₀.from _) ≫
        (nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ) ◁
          joinInr ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ)) Δ[0]) ≫
          (β_ _ _).hom ≫ uncurry (strictSemifreeCoconeFunctorFamily A SimplexCategoryᵒᵖ) := rfl

/-- U40の前提計算：指定apexは指定全余錐族の同じ共同評価である。 -/
lemma specifiedNativeApex_eq :
    strictSemifreeNativeApexFamily A SimplexCategoryᵒᵖ =
      lift (𝟙 _) (SSet.stdSimplex.isTerminalObj₀.from _) ≫
        (nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ) ◁
          joinInr ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ)) Δ[0]) ≫
          (β_ _ _).hom ≫ uncurry (strictSemifreeCoconeFunctorFamily A SimplexCategoryᵒᵖ) := by
  exact specifiedNativeApex_eq_aux A

/-- U40：計算済みapexと指定普遍余錐のapexの全関手同型。 -/
def strictSemifreeComputedNativeApexIso :
    FunctorIso (strictSemifreeComputedApexFamily A)
      (strictSemifreeNativeApexFamily A SimplexCategoryᵒᵖ) := by
  have e := (strictSemifreeComputedCoconeFamilyIso A).postcomp
    (coconeApexEvaluation
      ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))
  rw [coconeFamily_apex_evaluation, coconeFamily_apex_evaluation] at e
  rw [strictSemifreeComputedColimitFamily_evaluation] at e
  rw [specifiedNativeApex_eq]
  exact e

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
