module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowSourceEvaluationCofinality
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowTargetEvaluationFiltered
public import SerrePositivity.InfinityCategories.F2.Ind.LiftedPointQuillenA
public import SerrePositivity.InfinityCategories.F2.Ind.SmallDiagramCommaEvaluation
public import SerrePositivity.InfinityCategories.F2.Filtered.FilteredWeakContractibility
/-!
概要：元の射図式 comma と小さい表示添字の両端評価は right cofinal。
方針：指定変換下の実引き戻しの filtered 性と、元の点へ戻す Quillen A を使う。
規約：同じ元の評価写像を保持し、Kan 性やモデル圏の仮定を要求しない。
使われ方：射形状の元の標準全余錐の各点での余極限性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C)
/-- 概要：元の射図式 comma の終点評価は right cofinal。
方針：全 coslice 引き戻しの弱可縮性を使う。規約：元の写像を保持。使われ方：単一 filtered 表示の各点密度。 -/
lemma diagramCommaEvaluation_target_isRightCofinal :
    IsRightCofinal (diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  apply isRightCofinal_of_weaklyContractible_lifted_point_under
  intro z
  have := indArrowTargetEvaluationComma_isFiltered κ D
    (isKappaSmall_of_finite (Fact.out : κ.IsRegular).aleph0_le (Δ[0] : SSet.{u})) z
  exact isWeaklyContractible_of_isFilteredInfinity _
/-- 概要：小さい表示添字の持ち上げからの同じ終点評価も right cofinal。
方針：元の comma 同型と評価を合成する。規約：元の写像を保持。使われ方：単一 filtered 表示の各点密度。 -/
lemma smallDiagramCommaEvaluation_target_isRightCofinal :
    IsRightCofinal (smallDiagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  exact (isRightCofinal_of_isIso (smallDiagramCommaIso κ D).hom).comp
    (diagramCommaEvaluation_target_isRightCofinal κ D)
/-- 概要：元の全射図式 comma の任意の指定点での評価は right cofinal。
方針：区間の二頂点を列挙する。規約：元の写像を保持。使われ方：単一 filtered 表示の各点密度。 -/
lemma diagramCommaEvaluation_interval_isRightCofinal
    (k : (Δ[1] : SSet.{u}) _⦋0⦌) : IsRightCofinal (diagramCommaEvaluation κ D k) := by
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective k
  fin_cases i
  · exact diagramCommaEvaluation_source_isRightCofinal κ D
  · exact diagramCommaEvaluation_target_isRightCofinal κ D
/-- 概要：小さい表示添字からの任意の指定点での元の評価は right cofinal。
方針：同じ元の評価を同型で移す。規約：元の写像を保持。使われ方：単一 filtered 表示の各点密度。 -/
lemma smallDiagramCommaEvaluation_interval_isRightCofinal
    (k : (Δ[1] : SSet.{u}) _⦋0⦌) : IsRightCofinal (smallDiagramCommaEvaluation κ D k) :=
  (isRightCofinal_of_isIso (smallDiagramCommaIso κ D).hom).comp
    (diagramCommaEvaluation_interval_isRightCofinal κ D k)
end SerrePositivity.InfinityCategories.F2.Ind
