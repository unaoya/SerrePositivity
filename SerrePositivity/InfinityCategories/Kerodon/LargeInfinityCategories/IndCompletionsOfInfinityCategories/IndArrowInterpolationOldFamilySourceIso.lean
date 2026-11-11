module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FullyFaithfulSquareRelativeIsoReflection
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndArrowInterpolationSliceIsoProjection
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndArrowInterpolationSourceFamily
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DiagramCommaEvaluationSliceSquare
/-!
概要：元の補間旧族と q の同型を、始点評価後の元の等号同型との一致付きで回収する。
方針：同じ slice 比較を充満忠実な可換正方形に沿って実 comma へ反映する。
規約：元の両全族・指定同型の値を保持する。
使われ方：指定された下側変換を保つ under comma への帰還。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {κ : Cardinal.{u}} {C A : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C}
  {q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ D}
  (V : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndArrowInterpolationData κ D q)
/-- 概要：元の実 comma の旧族と q の同型は、始点評価で元の等号同型となる。
方針：同じ slice 同型の標準逆像を使う。
規約：評価後の指定値を保持。使われ方：指定下側変換との相対的な比較。 -/
lemma exists_indArrowInterpolationOldFamily_iso_source :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowInterpolationOldFamily V) q,
      d.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) =
        eqToIso (congrArg
          (fun v => SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowInterpolationOldFamily_source V)) := by
  obtain ⟨h, d, hd⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_indArrowInterpolationOldFamily_slice_iso_projection V
  let j := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaSliceProjection κ D
  let hj := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaSliceProjection_isFullyFaithful κ D
  let k := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaEvaluationSliceProjection κ D (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  let hk := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaEvaluationSliceProjection_isFullyFaithful κ D
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  refine ⟨hj.preimageFunctorIso d, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.fullyFaithful_preimage_functorIso_projection j hj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    _ k hk (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaEvaluation_slice_square κ D _) _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowInterpolationOldFamily_source V) d ?_⟩
  rw [hd]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isFunctorEqIso_eqToIso h
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
