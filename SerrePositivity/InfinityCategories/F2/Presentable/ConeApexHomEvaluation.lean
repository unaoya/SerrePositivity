module

public import SerrePositivity.InfinityCategories.F2.Presentable.ConeApexHomRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafCoconeFlip
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomEvaluationNaturality
public import SerrePositivity.InfinityCategories.F2.Presentable.ConstantPointFunctorIso

/-!
概要：全余錐から定値図式への射を右頂点で評価する対応の全単射。
方針：右端への制限と一点関手圏の評価同型を合成する。
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

/-- 概要：円錐から定値図式への Hom の右頂点評価は全単射。
方針：右端制限の全単射と一点関手圏の評価同型を合成する。
規約：元の評価関手の作用を使う。
使われ方：普遍余錐の Hom と頂点の Hom の比較。 -/
lemma coneApex_homEvaluation_bijective {K X : SSet.{u}} [Quasicategory X]
    (H : join K (Δ[0] : SSet.{u}) ⟶ X) (y : X _⦋0⦌) :
    Function.Bijective
      ((hoFunctor.map (evaluateFunctorAt (Y := X) (coconeRightApexVertex K))).toFunctor.map :
        FunctorHom H (SSet.const y) → _) := by
  let a := SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))
  have hv : IsIso (evaluateFunctorAt (Y := X) a) := by
    change IsIso (constantPointFunctorIso X).inv
    infer_instance
  have hb := (qCatEquivalenceOfIso (asIso (evaluateFunctorAt (Y := X) a))).isFullyFaithful
  have hp := coneApex_homRestriction_bijective H y
  have h := (hb.homotopyCategoryMap_bijective _ _).comp hp
  have hf : (pre (joinInr K (Δ[0] : SSet.{u}))).app X ≫ evaluateFunctorAt a =
      evaluateFunctorAt (Y := X) (coconeRightApexVertex K) := by
    rw [evaluateFunctorAt_precomp]
    congr 1
  have hh : (hoFunctor.map ((pre (joinInr K (Δ[0] : SSet.{u}))).app X)).toFunctor ⋙
      (hoFunctor.map (evaluateFunctorAt (Y := X) a)).toFunctor =
        (hoFunctor.map (evaluateFunctorAt (Y := X) (coconeRightApexVertex K))).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp, hf]
  change Function.Bijective
    (((hoFunctor.map ((pre (joinInr K (Δ[0] : SSet.{u}))).app X)).toFunctor ⋙
      (hoFunctor.map (evaluateFunctorAt (Y := X) a)).toFunctor).map :
        FunctorHom H (SSet.const y) → _) at h
  rw [hh] at h
  exact h

end SerrePositivity.InfinityCategories.F2.Presentable
