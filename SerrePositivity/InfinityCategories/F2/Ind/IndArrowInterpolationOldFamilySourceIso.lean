module

public import SerrePositivity.InfinityCategories.F2.Ind.FullyFaithfulSquareRelativeIsoReflection
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationSliceIsoProjection
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationSourceFamily
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramCommaEvaluationSliceSquare
/-!
概要：元の補間旧族と q の同型を、始点評価後の元の等号同型との一致付きで回収する。
方針：同じ slice 比較を充満忠実な可換正方形に沿って実 comma へ反映する。
規約：元の両全族・指定同型の値を保持する。
使われ方：指定された下側変換を保つ under comma への帰還。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {C A : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D}
  (V : IndArrowInterpolationData κ D q)
/-- 概要：元の実 comma の旧族と q の同型は、始点評価で元の等号同型となる。
方針：同じ slice 同型の標準逆像を使う。
規約：評価後の指定値を保持。使われ方：指定下側変換との相対的な比較。 -/
lemma exists_indArrowInterpolationOldFamily_iso_source :
    ∃ d : FunctorIso (indArrowInterpolationOldFamily V) q,
      d.postcomp (diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) =
        eqToIso (congrArg
          (fun v => SSet.HomotopyCategory.mk (functorVertex v))
          (indArrowInterpolationOldFamily_source V)) := by
  obtain ⟨h, d, hd⟩ := exists_indArrowInterpolationOldFamily_slice_iso_projection V
  let j := diagramCommaSliceProjection κ D
  let hj := diagramCommaSliceProjection_isFullyFaithful κ D
  let k := diagramCommaEvaluationSliceProjection κ D (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  let hk := diagramCommaEvaluationSliceProjection_isFullyFaithful κ D
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  refine ⟨hj.preimageFunctorIso d, fullyFaithful_preimage_functorIso_projection j hj
    (diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    _ k hk (diagramCommaEvaluation_slice_square κ D _) _ _
    (indArrowInterpolationOldFamily_source V) d ?_⟩
  rw [hd]
  exact isFunctorEqIso_eqToIso h
end SerrePositivity.InfinityCategories.F2.Ind
