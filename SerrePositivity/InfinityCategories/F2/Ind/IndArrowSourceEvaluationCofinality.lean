module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowSourceEvaluationFiltered
public import SerrePositivity.InfinityCategories.F2.Ind.LiftedPointQuillenA
public import SerrePositivity.InfinityCategories.F2.Ind.SmallDiagramCommaEvaluation
public import SerrePositivity.InfinityCategories.F2.Filtered.FilteredWeakContractibility
/-!
概要：元の射図式 comma と小さい表示添字の始点評価は right cofinal。
方針：指定変換下の余錐で実 coslice 引き戻しを filtered とし、元の点の Quillen A に戻す。
規約：同じ元の評価写像を使い、追加の Kan 性やモデル圏の仮定を要求しない。
使われ方：元の単一 filtered 射図式表示の始点での余極限性。
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
/-- 概要：元の全射図式 comma の始点評価は right cofinal。
方針：全 coslice 引き戻しの弱可縮性を使う。
規約：指定元図式 D を保持。使われ方：始点での元の標準余錐の余極限性。 -/
lemma diagramCommaEvaluation_source_isRightCofinal :
    IsRightCofinal (diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
  apply isRightCofinal_of_weaklyContractible_lifted_point_under
  intro z
  have := indArrowSourceEvaluationComma_isFiltered κ D
    (isKappaSmall_of_finite (Fact.out : κ.IsRegular).aleph0_le (Δ[0] : SSet.{u})) z
  exact isWeaklyContractible_of_isFilteredInfinity _
/-- 概要：同じ小さい表示添字の宇宙持ち上げからの元の始点評価も right cofinal。
方針：実 comma の同型と同じ評価を合成する。
規約：元の評価写像を保持。使われ方：単一小さい filtered 表示への接続。 -/
lemma smallDiagramCommaEvaluation_source_isRightCofinal :
    IsRightCofinal (smallDiagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
  exact (isRightCofinal_of_isIso (smallDiagramCommaIso κ D).hom).comp
    (diagramCommaEvaluation_source_isRightCofinal κ D)
end SerrePositivity.InfinityCategories.F2.Ind
