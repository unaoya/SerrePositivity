module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineNativeOrdinaryTargetUnit
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOrdinaryTotalCompatibility
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOriginalCoverTarget
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineCoverTargetAugmentation
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.NativeCompletedModelUnit
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.FiniteCompletionComplexHomExt
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineCoverResolvedTotal
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AssociatedCompletionComparison
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.CoverCompletionCoordinates
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOriginalCoverTarget
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOriginalCoverComparison
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineCoverOrdinaryComparison

/-!
# 元の指定e_targetと元の通常被覆比較の一致

## 概要
元の完備Tot比較から構成した終域同型が、元の通常係数比較を計算することを示す。

## 方針
同じ完備化単位上で、元の模型同型・Tot係数射・標準増大を照合し、一意性を使う。

## 規約
元のaffineOriginalCoverTargetIsoを再定義せず、別の同型に置き換えない。

## 使われ方
HT04.R2の指定終域同型を使う正方形。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DifferentialGraded.ScalarExtension DerivedCompletion HTComparisonTotal HTComparisonResolution
open HTUniversalCrystallineInput
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 元の座標比較の成分を、同じ指定された座標同型として読む。 -/
private theorem coverImageCompletionNatIso_inv_app_normalized
    (P : OrientedPrism p A) (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    (coverImageCompletionNatIso P).inv.app K =
      (associatedFiniteCompletionIso (coverImageCoordinates P)
        (fun _ : Fin 2 => (p : Construction61.crystallineCoverRing P))
        (coverImageCoordinates_associated P)
        (((ModuleCat.extendScalars (Construction61.crystallineCoverMap P).toRingHom).mapHomologicalComplex
          (.up ℤ)).obj K)).inv := rfl

/-- 元の標準単位を、元の被覆模型を終域に取る型で読む。 -/
private def coverOriginalModelUnit (P : OrientedPrism p A)
    (S : CochainComplex (ModuleCat.{u} A) ℤ) :
    DerivedCategory.Q.obj
      (((ModuleCat.extendScalars (Construction61.crystallineCoverMap P).toRingHom).mapHomologicalComplex
        (.up ℤ)).obj S) ⟶
      DerivedCategory.Q.obj ((Construction61.completedCoverModelFunctor P).obj S) :=
  DerivedCategory.Q.map (finiteCompletionUnit
    (fun _ : Fin 2 => (p : Construction61.crystallineCoverRing P))
    (((ModuleCat.extendScalars (Construction61.crystallineCoverMap P).toRingHom).mapHomologicalComplex
      (.up ℤ)).obj S))

/-- 同じ模型から完備な終域への射を、元の単位上で検査する。 -/
private theorem coverOriginalModelHom_ext (P : OrientedPrism p A)
    (S : CochainComplex (ModuleCat.{u} A) ℤ)
    (Y : DerivedCategory (ModuleCat.{u} (Construction61.crystallineCoverRing P)))
    (hY : IsComplete (Construction61.crystallineCoverRing P) (p : Construction61.crystallineCoverRing P) Y)
    {f g : DerivedCategory.Q.obj ((Construction61.completedCoverModelFunctor P).obj S) ⟶ Y}
    (h : coverOriginalModelUnit P S ≫ f = coverOriginalModelUnit P S ≫ g) : f = g := by
  apply finiteCompletionComplexHom_ext
    (fun _ : Fin 2 => (p : Construction61.crystallineCoverRing P))
    (((ModuleCat.extendScalars (Construction61.crystallineCoverMap P).toRingHom).mapHomologicalComplex
      (.up ℤ)).obj S) Y (fun _ => hY)
  exact h

/-- 元の指定された完備Tot終域同型は、同じ元の通常係数表示と一致する。 -/
theorem affineOriginalCoverTargetIso_eq_ordinary
    (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)
    (hF : IsCompletelyFlat (Ideal.span {Construction61.coverModPGenerator P})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) :
    (affineOriginalCoverTargetIso P hP r hF hR).hom =
      (affineCoverOrdinaryComparison P r).app (affineHTTotalComplex P hP r) ≫
        DerivedCategory.Q.map (affineAnyOrdinaryTotalIso (Construction61.crystallineCoverMap P) hP
          (Construction61.crystallineCover_bounded P) (Construction61.crystallineCover_generator P) r).hom := by
  let B : Type u := Construction61.crystallineCoverRing P
  let Q := Construction61.crystallineCover P
  let hQ := Construction61.crystallineCover_bounded P
  let f := Construction61.crystallineCoverMap P
  let E := (ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (.up ℤ)
  let z := fun _ : Fin 2 => (p : B)
  let K := affineComplexOnBase P r (affineHTTotalComplex P hP r)
  let S := (complexResolutionFunctor A).obj K
  let q : S ⟶ K := (complexResolutionAugmentation A).app K
  let o := affineAnyOrdinaryTotalIso f hP hQ (Construction61.crystallineCover_generator P) r
  let F := finiteDerivedCompletionFunctor (coverImageCoordinates P)
  let D := complexDerivedExtension f.toRingHom
  let X := affineBaseSingleRows P hP r
  let eP := affineBaseSingleTotalPolynomialIso P hP r
  let eQ := affineBaseSingleTotalPolynomialIso Q hQ r
  let c := (coverImageCompletionNatIso P).app S
  let n := nativeCompletedScalarModelIso f.toRingHom ![(p : A), P.generator] q
    (complexResolutionAugmentation_quasiIso A K) (complexResolutionFunctor_kFlat A K)
  let v := cosimplicialNativeCompletedBaseChangeComparison f.toRingHom ![(p : A), P.generator]
    X 0 (affineBaseSingleRows_lowerBound P hP r)
  let t := affineCoverResolvedTotalIso P hP r
  have he : (affineOriginalCoverTargetIso P hP r hF hR).hom =
      c.inv ≫ n.inv ≫ (F.map (D.map (DerivedCategory.Q.map eP.inv)) ≫ v) ≫
        t.hom ≫ DerivedCategory.Q.map eQ.hom := by
    rfl
  have h := affineNativeOrdinaryTarget_unit f hP hQ (Construction61.crystallineCover_generator P)
    r ![(p : A), P.generator] z (coverImageCoordinates_associated P)
    (affineReducedCover_scalarExtensionTorVanishing P hP r) (affineCoverRows_complete P r)
  have hs : DerivedCategory.Q.map (finiteCompletionUnit z (E.obj S)) ≫
      (affineCoverOrdinaryComparison P r).app (affineHTTotalComplex P hP r) =
      DerivedCategory.Q.map (E.map q) :=
    unit_comp_resolvedOrdinaryComparison f.toRingHom z (affineRestrictedComplexFunctor P r)
      (fun K _ => affineCoverBaseChange_complete_p P r K) (affineHTTotalComplex P hP r)
  have hs' := congrArg (fun (k : DerivedCategory.Q.obj (E.obj S) ⟶ DerivedCategory.Q.obj (E.obj K)) =>
    k ≫ DerivedCategory.Q.map o.hom) hs.symm
  dsimp only [F, D, X, eP, eQ, n, v, t, K, S, q, E, o, f, Q, hQ, B, z,
    affineCoverResolvedTotalIso, affineBaseSingleRows, coverImageCoordinates] at h hs'
  have hfinal := h.trans hs'
  have hc := coverImageCompletionNatIso_inv_app_normalized P S
  simp only [c, Iso.app_inv] at he
  have hc' := congrArg (fun k => k ≫ n.inv ≫
    (F.map (D.map (DerivedCategory.Q.map eP.inv)) ≫ v) ≫ t.hom ≫ DerivedCategory.Q.map eQ.hom) hc
  simp only [Category.assoc] at he hc' hfinal
  have hec := he.trans hc'
  let u := coverOriginalModelUnit P S
  have hecu := congrArg (fun k => u ≫ k) hec
  dsimp only [u, F, D, X, eP, eQ, n, v, t, K, S, q, E, o, f, Q, hQ, B, z,
    coverOriginalModelUnit, affineCoverResolvedTotalIso, affineBaseSingleRows, coverImageCoordinates,
    Construction61.completedCoverModelFunctor, finiteCompletionFunctor,
    Functor.comp_obj, Functor.id_obj] at hecu hfinal
  try simp (config := {zetaDelta := true}) only [coverOriginalModelUnit,
    affineCoverResolvedTotalIso, affineBaseSingleRows, coverImageCoordinates,
    Construction61.completedCoverModelFunctor, finiteCompletionFunctor,
    Functor.comp_obj, Functor.id_obj, Functor.map_comp, Category.assoc] at hecu
  try simp (config := {zetaDelta := true}) only [coverOriginalModelUnit,
    affineCoverResolvedTotalIso, affineBaseSingleRows, coverImageCoordinates,
    Construction61.completedCoverModelFunctor, finiteCompletionFunctor,
    Functor.comp_obj, Functor.id_obj, Functor.map_comp, Category.assoc] at hfinal
  have hwhole := Eq.trans hecu hfinal
  apply coverOriginalModelHom_ext P S
    (DerivedCategory.Q.obj (affineComplexOnBase Q r (affineHTTotalComplex Q hQ r)))
    (affineHTTotal_complete_p Q hQ r)
  simpa only [F, D, X, eP, eQ, n, v, t, K, S, q, E, o, f, Q, hQ, B, z,
    coverOriginalModelUnit, affineCoverResolvedTotalIso, affineBaseSingleRows, coverImageCoordinates,
    Construction61.completedCoverModelFunctor, finiteCompletionFunctor,
    Functor.comp_obj, Functor.id_obj, Category.assoc] using hwhole

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
