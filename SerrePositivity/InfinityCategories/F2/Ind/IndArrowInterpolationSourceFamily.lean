module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationSourceValues
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramCommaEvaluation
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramConePointUncurry
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationOldCocone
/-!
概要：補間した実 comma の全族と旧部分の始点評価を厳密に回収する。
方針：小さい図式への射影と全余錐の uncurry の二成分で確認する。
規約：元の指定始点余錐と元の q を保持。使われ方：指定始点下の相対反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {C A : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D}
  (V : IndArrowInterpolationData κ D q)
/-- 概要：補間した元の全族の始点評価は、指定始点余錐の同じ点制限。
方針：射影と全余錐の二成分で確認する。
規約：元の全射と指定値を保持する。
使われ方：指定始点下の実 comma の相対反映。 -/
lemma indArrowInterpolationCommaFamily_source :
    indArrowInterpolationCommaFamily V ≫
      diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)) =
    V.sourceCone ≫
      diagramConePointRestriction κ D (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, diagramCommaEvaluation_projection,
      diagramConePointRestriction_projection]
    rw [← Category.assoc, indArrowInterpolationCommaFamily_projection]
    exact indArrowInterpolationSmallDiagram_source V
  · apply sliceOverUncurry_injective
    simp only [Category.assoc]
    rw [diagramCommaEvaluation_uncurry, diagramConePointRestriction_uncurry,
      indArrowInterpolationCommaFamily_uncurry]
    exact indArrowInterpolationLiftedCoconeMap_source V
/-- 概要：元の試験族への制限は、始点で元の q と厳密に一致する。
方針：全族の評価と指定された制限条件を使う。
規約：元の全射と指定値を保持する。
使われ方：指定始点下の実 comma の相対反映。 -/
lemma indArrowInterpolationOldFamily_source : indArrowInterpolationOldFamily V ≫
    diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)) =
    q ≫ diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)) := by
  rw [indArrowInterpolationOldFamily, Category.assoc, indArrowInterpolationCommaFamily_source,
    ← Category.assoc]
  exact V.sourceRestriction
end SerrePositivity.InfinityCategories.F2.Ind
