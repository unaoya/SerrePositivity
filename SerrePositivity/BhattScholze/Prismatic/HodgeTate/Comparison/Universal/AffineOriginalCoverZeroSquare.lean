module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOriginalCoverHomologyIsos
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOriginalCoverHomologyIsos
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineLineOrdinaryBaseHomology
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOrdinaryTarget

/-!
# 元の指定e_targetを使う零次の正方形

## 概要
元の同じηの完備被覆像の零次を、元の標準HT写像と指定同型で照合する。

## 方針
元の導来正方形を標準ホモロジー比較で移し、元の通常係数の零次の等式を使う。

## 規約
元の指定終域同型を通常係数の別の同型に置き換えない。

## 使われ方
HT04.R2の零次の型つきの正方形。
-/

public noncomputable section
universe u
open CategoryTheory HomologicalComplex
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded HTComparisonResolution HTUniversalCrystallineInput
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 同じ元のηの完備被覆像の零次の、元の指定e_targetによる正方形。 -/
theorem affineOriginalCover_zero_square
    (P : OrientedPrism p A) (hP : IsBoundedPrism P)
    (hF : IsCompletelyFlat (Ideal.span {Construction61.coverModPGenerator P})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal))
    (η : affineLineFormalModel P ⟶ affineHTTotalComplex P hP 1)
    (h0 : (affineLineFormalZeroIso P).hom ≫ homologyMap η 0 =
      ModuleCat.ofHom (affineHTTotalMap P hP 1 0)) :
    letI := Module.compHom (affineForms (Construction61.crystallineCover P) 1 0)
      (affineBaseToPolynomialMap (Construction61.crystallineCover P) 1)
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (Construction61.crystallineCoverRing P)) 0).map
      (DerivedCategory.Q.map ((Construction61.completedCoverModelFunctor P).map
        ((complexResolutionFunctor A).map ((affineRestrictedComplexFunctor P 1).map η)))) ≫
      (affineOriginalCoverTargetHomologyIso P hP 1 hF hR 0).hom =
    (affineOriginalCoverSourceZeroIso P hP).hom ≫
      ModuleCat.ofHom (affineBaseHTMap (Construction61.crystallineCover P)
        (Construction61.crystallineCover_bounded P) 1 0) := by
  let B : Type u := Construction61.crystallineCoverRing P
  let Q := Construction61.crystallineCover P
  let hQ := Construction61.crystallineCover_bounded P
  let f := Construction61.crystallineCoverMap P
  letI := Module.compHom (affineForms Q 1 0) (affineBaseToPolynomialMap Q 1)
  let τ := DerivedCategory.Q.map ((Construction61.completedCoverModelFunctor P).map
    ((complexResolutionFunctor A).map ((affineRestrictedComplexFunctor P 1).map η)))
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0
  let s := (affineCoverOrdinaryComparison P 1).app (affineLineFormalModel P)
  let t := affineOriginalCoverTargetIso P hP 1 hF hR
  let b := affineOriginalBaseComplexIso Q hQ 1
  let g := affineLineOrdinaryBaseRealization f hP hQ (Construction61.crystallineCover_generator P) η
  let e := (affineBaseComplex Q hQ 1).extendHomologyIso
    ComplexShape.embeddingUpNat (j := 0) (j' := (0 : ℤ)) rfl
  have hf : τ ≫ (t.hom ≫ DerivedCategory.Q.map b.hom) = s ≫ DerivedCategory.Q.map g := by
    have hg : ((affineOrdinaryCoverFunctor P 1).map η) ≫
        (affineAnyOrdinaryTotalIso f hP hQ (Construction61.crystallineCover_generator P) 1).hom ≫
          b.hom = g := by
      simp only [b, g, Q, hQ, f, affineAnyOrdinaryTotalIso, affineLineOrdinaryBaseRealization,
        Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
        Iso.inv_hom_id, Category.comp_id, Functor.map_comp,
        ComplexShape.Embedding.extendFunctor_map, Functor.comp_map]
    have h := congrArg (fun q => q ≫ DerivedCategory.Q.map b.hom)
      (affineCompletedCover_ordinary_square P hP hF hR η)
    have h' : τ ≫ (t.hom ≫ DerivedCategory.Q.map b.hom) =
        s ≫ DerivedCategory.Q.map (((affineOrdinaryCoverFunctor P 1).map η) ≫
          (affineAnyOrdinaryTotalIso f hP hQ (Construction61.crystallineCover_generator P) 1).hom ≫
          b.hom) := by
      simpa only [τ, t, s, f, hQ, Category.assoc, ← Functor.map_comp] using h
    exact h'.trans (congrArg (fun q => s ≫ DerivedCategory.Q.map q) hg)
  have hh := derivedHomologyComparison_square τ g s (t.hom ≫ DerivedCategory.Q.map b.hom) hf 0
  simp only [Functor.map_comp, Category.assoc,
    DerivedCategory.homologyFunctorFactors_hom_naturality] at hh
  have hz := affineLineOrdinaryBaseRealization_zero_square f hP hQ
    (Construction61.crystallineCover_generator P) η h0 (affineCoverFormsEquiv P 0)
    (affineCoverFormsEquiv_basis P 0)
  have hz' : homologyMap g 0 ≫ e.hom =
      (affineLineFormalOrdinaryZeroIso P f.toRingHom).inv ≫
        (affineCoverFormsEquiv P 0).toModuleIso.hom ≫ ModuleCat.ofHom (affineBaseHTMap Q hQ 1 0) := by
    apply (cancel_epi (affineLineFormalOrdinaryZeroIso P f.toRingHom).hom).mp
    simpa only [Q, hQ, f, g, e, LinearEquiv.toModuleIso,
      Category.assoc, Iso.hom_inv_id_assoc] using hz
  have hpost := congrArg (fun k => k ≫ e.hom) hh
  simp only [Functor.map_comp, Category.assoc] at hpost
  have hzpost := congrArg (fun k => H.map s ≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) 0).hom.app
      ((affineOrdinaryCoverFunctor P 1).obj (affineLineFormalModel P)) ≫ k) hz'
  have hfinal := hpost.trans hzpost
  simpa only [B, Q, hQ, f, τ, H, s, t, b, e, affineOriginalCoverTargetHomologyIso, affineOriginalCoverSourceZeroIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom, Iso.app_hom,
    HomologicalComplex.homologyFunctor_map, Int.natCast_zero, Int.natCast_one,
    Category.assoc] using hfinal

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
