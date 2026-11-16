module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineReducedCoverProjection

/-!
# 元の被覆底変換後の商射のH⁰の全射性

## 概要
元の二座標完備底変換後の商射は、H⁰で全射となる。

## 方針
指定されたfull・剰余被覆同型の商射の正方形と、元の加群の商射の全射性を使う。

## 規約
導来圏全体でのエピ射とは主張しない。

## 使われ方
元の剰余被覆同型の項ごとの一致をH⁰上で降ろす。
-/

public noncomputable section
universe u
open CategoryTheory
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

/-- 離散対象の元のエピ射を零次に置くと、その元のH⁰写像はエピ射となる。 -/
theorem singleHomologyZero_epi {R : Type u} [CommRing R]
    {M N : ModuleCat.{u} R} (f : M ⟶ N) [Epi f] :
    Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map f)) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} R) 0
  let e := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0
  have hn : H.map (S.map f) ≫ e.hom.app N = e.hom.app M ≫ f := e.hom.naturality f
  have he : Epi (H.map (S.map f) ≫ e.hom.app N) := by
    rw [hn]
    infer_instance
  exact (epi_comp_iff_of_isIso _ _).mp he

/-- 元の二座標完備底変換で写した元の商射はH⁰で全射。 -/
theorem affineFullBaseProjection_cover_homology_epi {p : ℕ} [Fact p.Prime]
    {A : Type u} [CommRing A] (P : OrientedPrism p A) (hP : IsBoundedPrism P)
    (r : ℕ) (n : SimplexCategory) :
    let B : Type u := Construction61.crystallineCoverRing P
    let G := boundedAboveDerivedBaseChange (Construction61.crystallineCoverMap P).toRingHom ⋙
      boundedAboveDerivedCompletionFunctor B (p : B) ⋙
      boundedAboveDerivedCompletionFunctor B (p : B)
    Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).map
      (G.map (boundedAboveDerivedSingleFunctor.map ((affineFullBaseProjection P hP r).app n))).hom) := by
  let B : Type u := Construction61.crystallineCoverRing P
  let Q := Construction61.crystallineCover P
  let hQ := Construction61.crystallineCover_bounded P
  let G := boundedAboveDerivedBaseChange (Construction61.crystallineCoverMap P).toRingHom ⋙
    boundedAboveDerivedCompletionFunctor B (p : B) ⋙ boundedAboveDerivedCompletionFunctor B (p : B)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0
  let q := (G.map (boundedAboveDerivedSingleFunctor.map ((affineFullBaseProjection P hP r).app n))).hom
  haveI := (affineFullBaseReduction_shortExact Q hQ r n).epi_g
  haveI := singleHomologyZero_epi ((affineFullBaseProjection Q hQ r).app n)
  have hp := congrArg H.map (affineReducedCoverTermIso_projection P hP r n)
  simp only [Functor.map_comp] at hp
  have he : Epi (H.map q ≫ H.map (affineReducedCoverTermIso P hP r n).hom) := by
    rw [hp]
    change Epi (H.map (affineFullCoverTermIso P hP r n).hom ≫ H.map
      ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map
        ((affineFullBaseProjection Q hQ r).app n)))
    infer_instance
  exact (epi_comp_iff_of_isIso _ _).mp he

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
