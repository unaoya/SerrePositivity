module

public import SerrePositivity.InfinityCategories.F2.Presentable.LeftConeHomRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafCoconeFlip
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomEvaluationNaturality
public import SerrePositivity.InfinityCategories.F2.Presentable.ConstantPointFunctorIso

/-!
概要：定値図式から全錐への射を左頂点で評価する対応の全単射。
方針：左端への制限と一点関手圏の評価同型を合成する。
規約：標的のみを quasicategory とする。
使われ方：余極限単位による Hom 対応。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：定値図式から錐への Hom の左頂点評価は全単射。
方針：左端制限の全単射と一点関手圏の評価同型を合成する。
規約：元の評価関手の作用を使う。
使われ方：普遍錐の Hom と頂点の Hom の比較。 -/
lemma leftConeApex_homEvaluation_bijective {K X : SSet.{u}} [Quasicategory X]
    (H : join (Δ[0] : SSet.{u}) K ⟶ X) (y : X _⦋0⦌) :
    Function.Bijective
      ((hoFunctor.map (evaluateFunctorAt (Y := X)
        (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) K)))).toFunctor.map :
        FunctorHom (SSet.const y) H → _) := by
  let a := SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))
  have hv : IsIso (evaluateFunctorAt (Y := X) a) := by
    change IsIso (constantPointFunctorIso X).inv
    infer_instance
  have hb := (qCatEquivalenceOfIso (asIso (evaluateFunctorAt (Y := X) a))).isFullyFaithful
  have hp := leftConeApex_homRestriction_bijective H y
  have h := (hb.homotopyCategoryMap_bijective _ _).comp hp
  have hf : (pre (joinInl (Δ[0] : SSet.{u}) K)).app X ≫ evaluateFunctorAt a =
      evaluateFunctorAt (Y := X) (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) K)) := by
    rw [evaluateFunctorAt_precomp]
    congr 1
  have hh : (hoFunctor.map ((pre (joinInl (Δ[0] : SSet.{u}) K)).app X)).toFunctor ⋙
      (hoFunctor.map (evaluateFunctorAt (Y := X) a)).toFunctor =
        (hoFunctor.map (evaluateFunctorAt (Y := X)
          (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) K)))).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp, hf]
  change Function.Bijective
    (((hoFunctor.map ((pre (joinInl (Δ[0] : SSet.{u}) K)).app X)).toFunctor ⋙
      (hoFunctor.map (evaluateFunctorAt (Y := X) a)).toFunctor).map :
        FunctorHom (SSet.const y) H → _) at h
  rw [hh] at h
  exact h

end SerrePositivity.InfinityCategories.F2.Presentable
