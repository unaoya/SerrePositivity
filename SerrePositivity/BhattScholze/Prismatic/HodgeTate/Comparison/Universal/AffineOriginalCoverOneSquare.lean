module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOriginalCoverHomologyIsos
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOriginalCoverHomologyIsos
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineLineOrdinaryBaseHomology
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOrdinaryTarget

/-!
# 元の指定e_targetを使う一次の正方形

## 概要
元の同じηの完備被覆像の一次を、元の標準HT写像と指定同型で照合する。

## 方針
元の導来正方形を標準ホモロジー比較で移し、元の通常係数の一次の等式と向きの単位の逆を使う。

## 規約
元の指定終域同型を通常係数の別の同型に置き換えない。

## 使われ方
HT04.R2の一次の型つきの正方形。
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

/-- 同じ元のηの完備被覆像の一次の、元の指定e_targetによる正方形。 -/
theorem affineOriginalCover_one_square
    (P : OrientedPrism p A) (hP : IsBoundedPrism P)
    (hF : IsCompletelyFlat (Ideal.span {Construction61.coverModPGenerator P})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal))
    (η : affineLineFormalModel P ⟶ affineHTTotalComplex P hP 1)
    (h1 : (affineLineFormalOneIso P).hom ≫ homologyMap η 1 =
      ModuleCat.ofHom (affineHTTotalMap P hP 1 1)) :
    letI := Module.compHom (affineForms (Construction61.crystallineCover P) 1 1)
      (affineBaseToPolynomialMap (Construction61.crystallineCover P) 1)
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (Construction61.crystallineCoverRing P)) 1).map
      (DerivedCategory.Q.map ((Construction61.completedCoverModelFunctor P).map
        ((complexResolutionFunctor A).map ((affineRestrictedComplexFunctor P 1).map η)))) ≫
      (affineOriginalCoverTargetHomologyIso P hP 1 hF hR 1).hom =
    (affineOriginalCoverSourceOneIso P hP).hom ≫
      ModuleCat.ofHom
        ((((((Construction61.crystallineCoverMap P).existsUnique_generator_unit.choose)⁻¹ :
          (Construction61.crystallineCoverRing P)ˣ) : Construction61.crystallineCoverRing P) •
          affineBaseHTMap (Construction61.crystallineCover P) (Construction61.crystallineCover_bounded P) 1 1) :
          affineForms (Construction61.crystallineCover P) 1 1 →ₗ[Construction61.crystallineCoverRing P]
            (affineBaseComplex (Construction61.crystallineCover P) (Construction61.crystallineCover_bounded P) 1).homology 1) := by
  let B : Type u := Construction61.crystallineCoverRing P
  let Q := Construction61.crystallineCover P
  let hQ := Construction61.crystallineCover_bounded P
  let f := Construction61.crystallineCoverMap P
  let v := f.existsUnique_generator_unit.choose
  have hv : f.toRingHom P.generator = Q.generator * (v : B) := f.existsUnique_generator_unit.choose_spec.1
  letI := Module.compHom (affineForms Q 1 1) (affineBaseToPolynomialMap Q 1)
  let τ := DerivedCategory.Q.map ((Construction61.completedCoverModelFunctor P).map
    ((complexResolutionFunctor A).map ((affineRestrictedComplexFunctor P 1).map η)))
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) 1
  let s := (affineCoverOrdinaryComparison P 1).app (affineLineFormalModel P)
  let t := affineOriginalCoverTargetIso P hP 1 hF hR
  let b := affineOriginalBaseComplexIso Q hQ 1
  let g := affineLineOrdinaryBaseRealization f hP hQ (Construction61.crystallineCover_generator P) η
  let e := (affineBaseComplex Q hQ 1).extendHomologyIso
    ComplexShape.embeddingUpNat (j := 1) (j' := (1 : ℤ)) rfl
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
  have hh := derivedHomologyComparison_square τ g s (t.hom ≫ DerivedCategory.Q.map b.hom) hf 1
  simp only [Functor.map_comp, Category.assoc,
    DerivedCategory.homologyFunctorFactors_hom_naturality] at hh
  have hz := affineLineOrdinaryBaseRealization_one_square f hP hQ
    (Construction61.crystallineCover_generator P) η h1 v hv (affineCoverFormsEquiv P 1)
    (affineCoverFormsEquiv_basis P 1)
  have hz' : homologyMap g 1 ≫ e.hom =
      (affineLineFormalOrdinaryOneIso P f.toRingHom).inv ≫
        (affineCoverFormsEquiv P 1).toModuleIso.hom ≫ ModuleCat.ofHom ((((v⁻¹ : Bˣ) : B) • affineBaseHTMap Q hQ 1 1) :
          affineForms Q 1 1 →ₗ[B] (affineBaseComplex Q hQ 1).homology 1) := by
    apply (cancel_epi (affineLineFormalOrdinaryOneIso P f.toRingHom).hom).mp
    simpa only [Q, hQ, f, g, e, LinearEquiv.toModuleIso,
      Category.assoc, Iso.hom_inv_id_assoc] using hz
  have hpost := congrArg (fun k => k ≫ e.hom) hh
  simp only [Functor.map_comp, Category.assoc] at hpost
  have hzpost := congrArg (fun k => H.map s ≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) 1).hom.app
      ((affineOrdinaryCoverFunctor P 1).obj (affineLineFormalModel P)) ≫ k) hz'
  have hfinal := hpost.trans hzpost
  simpa only [B, Q, hQ, f, v, τ, H, s, t, b, e, affineOriginalCoverTargetHomologyIso, affineOriginalCoverSourceOneIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom, Iso.app_hom,
    HomologicalComplex.homologyFunctor_map, Int.natCast_zero, Int.natCast_one,
    Category.assoc] using hfinal

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
