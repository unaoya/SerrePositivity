module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.BoundedScalarConeRightLeg
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineReducedCoverTerms
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineReducedCone
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineReducedCoverTerms
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic

/-!
# 元の剰余錐の指定同型と元の商射

## 概要
元の剰余錐の指定同型は右脚を元の商射へ送る。

## 方針
元の局所化比較の右脚、等式による錐の移送、元の短完全列の錐の射を使う。

## 規約
元のaffineReducedScalarConeIsoと元のaffineFullBaseProjectionを使う。

## 使われ方
指定された被覆底変換の同型を元の商射と照合する。
-/

public noncomputable section
universe u
open CategoryTheory
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 元の剰余錐の同型は、同じ元の商射を保つ。 -/
theorem affineReducedScalarConeIso_rightLeg
    (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ) (n : SimplexCategory) :
    (derivedScalarConeRightLeg A P.generator).app
        ((moduleObjectFunctor A).obj ((affineFullBaseModules P hP r).obj n)) ≫
      (affineReducedScalarConeIso P hP r n).hom =
    (moduleObjectFunctor A).map ((affineFullBaseProjection P hP r).app n) := by
  let F := CochainComplex.singleFunctor (ModuleCat.{u} A) 0
  let S := (affineFullBaseReduction P hP r n).map F
  have h : smulId P.generator (F.obj ((affineFullBaseModules P hP r).obj n)) =
      S.f := by
    change smulId P.generator _ = F.map (P.generator • 𝟙 _)
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
    rfl
  have hc := coneRightLeg_eqToHom h
  simp only [affineReducedScalarConeIso, Iso.trans_hom, asIso_hom, Iso.app_hom]
  erw [← Category.assoc, derivedScalarConeRightLeg_comparison]
  rw [← Category.assoc]
  change (DerivedCategory.Q.map (CochainComplex.mappingCone.inr
      (smulId P.generator (F.obj ((affineFullBaseModules P hP r).obj n)))) ≫
      eqToHom (congrArg (fun k => DerivedCategory.Q.obj (CochainComplex.mappingCone k)) h)) ≫
      DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S) = _
  rw [hc, ← Functor.map_comp, CochainComplex.mappingCone.inr_descShortComplex]
  rfl

/-- 元の単位の向きの変更の導来同型も、同じ右脚を保つ。 -/
theorem derivedScalarConeOrientationSingleIso_rightLeg {R : Type u} [CommRing R]
    (a : R) (v : Rˣ) (M : ModuleCat.{u} R) :
    (derivedScalarConeRightLeg R (a * (v : R))).app ((moduleObjectFunctor R).obj M) ≫
      (derivedScalarConeOrientationSingleIso a v M).hom =
    (derivedScalarConeRightLeg R a).app ((moduleObjectFunctor R).obj M) := by
  simp only [derivedScalarConeOrientationSingleIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  erw [← Category.assoc, derivedScalarConeRightLeg_comparison, ← Category.assoc,
    ← Functor.map_comp, scalarConeOrientationIso_inr]
  have hl := derivedScalarConeRightLeg_comparison R a
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)
  simp only [← hl, Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]
  rfl

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
