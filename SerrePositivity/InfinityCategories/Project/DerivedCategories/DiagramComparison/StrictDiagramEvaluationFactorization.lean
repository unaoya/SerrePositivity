module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ComplexDerivedQuasiIsomorphisms
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramLocalization
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalencePathInternalHom
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences

import all Mathlib.CategoryTheory.Types.Basic
import all Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import all Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
概要：元のstrict複体図式の全評価をobjectwise擬同型の∞局所化から因子化する。
方針：指定辺を各点で評価して反転を確認し、全関手圏の普遍性で延長する。
規約：全射列の評価とのFunctorIsoを返す。評価同値の充満忠実性と本質的全射性は別工程。
使われ方：3b-3 R5、HTT 4.2.4.4の比較射と元のstrict図式の評価の接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)

/-- 全strict図式の評価を固定添字で読むと、元の同じ通常評価のnerveになる。 -/
lemma strictComplexDiagramFamily_evaluation (j : strictDiagramIndex d) :
    strictComplexDiagramFamily A d ≫ evaluateFunctorAt
        (ULift.up (ComposableArrows.mk₀ j)) =
    nerveMap ((CategoryTheory.evaluation (strictDiagramIndex d) (Complex A)).obj j) ≫
      complexDerivedEvaluation A := by
  rw [strictComplexDiagramFamily, curry_evaluateFunctorAt_vertex]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change (complexDerivedEvaluation A).app (Opposite.op ⦋n⦌) _ =
    (complexDerivedEvaluation A).app (Opposite.op ⦋n⦌) _
  congr 1
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro i
    rfl
  intro i k f
  change (s.obj i).map (𝟙 j) ≫ (s.map f).app j = (s.map f).app j
  simp

/-- 元の全評価は、指定したobjectwise擬同型の辺を各点で可逆にする。 -/
lemma strictComplexDiagramFamily_inverts :
    InvertsEdges (strictComplexDiagramFamily A d) (strictDiagramWeakEdges A d) := by
  intro s hs
  obtain ⟨F, G, f, rfl⟩ := ComposableArrows.mk₁_surjective s
  apply (isInvertibleEdge_iff_evaluateFunctorAt_any _).mpr
  rintro ⟨v⟩
  obtain ⟨j, rfl⟩ := nerveEquiv.symm.surjective v
  have : QuasiIso (f.app j) := hs j
  have h := complexDerivedEvaluation_inverts_quasiIso A (f.app j)
  apply (isInvertibleEdge_congr (f := edgeOfSimplex
    ((complexDerivedEvaluation A).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ (f.app j)))) ?_).mpr h
  change (strictComplexDiagramFamily A d ≫ evaluateFunctorAt
    (ULift.up (ComposableArrows.mk₀ j))).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f) = _
  rw [strictComplexDiagramFamily_evaluation]
  change (complexDerivedEvaluation A).app (Opposite.op ⦋1⦌)
    ((nerveMap ((CategoryTheory.evaluation (strictDiagramIndex d) (Complex A)).obj j)).app
      (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f)) =
    (complexDerivedEvaluation A).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ (f.app j))
  rw [nerveMap_app_mk₁]
  rfl

/-- 局所化からの実評価と、元の全strict図式評価との全関手同型の存在。 -/
theorem exists_strictDiagramEvaluation_factor :
    ∃ ev : StrictDiagramInfinity A d ⟶
        (ihom ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve (strictDiagramIndex d)))).obj
          (derivedInfinityCategory A),
      Nonempty (FunctorIso (strictDiagramLocalization A d ≫ ev) (strictComplexDiagramFamily A d)) :=
  (strictDiagramLocalization_isLocalization A d).exists_extension
    (strictComplexDiagramFamily A d) (strictComplexDiagramFamily_inverts A d)

/-- 指定された局所化から、同じD(A)のcoherent図式への実比較写像。 -/
def strictDiagramDerivedEvaluation : StrictDiagramInfinity A d ⟶
    (ihom ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve (strictDiagramIndex d)))).obj
      (derivedInfinityCategory A) :=
  (exists_strictDiagramEvaluation_factor A d).choose

/-- 局所化の比較射は、元のstrict図式の全射列の評価と全関手同型で結ばれる。 -/
def strictDiagramDerivedEvaluation_factor :
    FunctorIso (strictDiagramLocalization A d ≫ strictDiagramDerivedEvaluation A d)
      (strictComplexDiagramFamily A d) :=
  (exists_strictDiagramEvaluation_factor A d).choose_spec.some

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
