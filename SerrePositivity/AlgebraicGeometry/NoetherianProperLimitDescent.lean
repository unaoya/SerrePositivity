module

public import SerrePositivity.AlgebraicGeometry.NoetherianProperDomination
public import SerrePositivity.AlgebraicGeometry.ProperDominationBaseChange
public import SerrePositivity.AlgebraicGeometry.FlatStageClosedImmersionLimit
public import SerrePositivity.AlgebraicGeometry.ClosedPullbackComposite

/-!
概要：Noether な有限段の対象について、極限での固有性を後段へ降ろす。
方針：Chow の固有支配の周辺への immersion を、極限で閉埋め込みにして C04 で降ろす。
規約：元の極限の環や射に Noether 性を要求しない。
使われ方：B01 の有限型係数段上の一般の固有模型の供給。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- Noether な段の分離的有限型射の極限での固有性は、ある後段へ降りる。 -/
theorem exists_isProper_pullback_of_isLimit_of_noetherian_source
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {j k} (a : j ⟶ k), IsAffineHom (D.map a)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    {i : J} [IsAffine (D.obj i)] {X : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ D.obj i) [IsSeparated f] [LocallyOfFiniteType f]
    [IsProper (pullback.snd f (c.π.app i))] :
    ∃ (j : J) (a : j ⟶ i), IsProper (pullback.snd f (D.map a)) := by
  obtain ⟨T, P, h, t, q, hh, hs, ht, hq, hcomm⟩ := exists_noetherian_proper_domination f
  letI : IsProper h := hh
  letI : Surjective h := hs
  letI : IsOpenImmersion t := ht
  letI : IsProper q := hq
  letI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace h
  letI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian h
  letI : IsNoetherian T := ⟨⟩
  let g := c.π.app i
  let a := pullback.snd g q
  let x := pullback.fst g q
  have hpb : IsPullback a x q g := (IsPullback.of_hasPullback g q).flip
  haveI : IsProper (pullback.fst g f) := by
    have H : IsProper ((pullbackSymmetry g f).hom ≫ pullback.snd f g) := inferInstance
    simpa only [pullbackSymmetry_hom_comp_snd] using H
  haveI : IsClosedImmersion (pullback.fst a t) :=
    isClosedImmersion_dominationBaseChangeProjection f h t q hcomm g
  haveI : IsClosedImmersion (pullback.snd t a) := by
    have H : IsClosedImmersion ((pullbackSymmetry t a).hom ≫ pullback.fst a t) := inferInstance
    simpa only [pullbackSymmetry_hom_comp_fst] using H
  haveI : IsClosedImmersion (pullback.snd t (a ≫ 𝟙 P)) :=
    isClosedImmersion_pullback_snd_of_composite t a (𝟙 _) (a ≫ 𝟙 P) (by simp)
  obtain ⟨j, hj⟩ := exists_closedImmersion_flatStageProjection_of_isLimit
    D c hc i a x q hpb (𝟙 P) t
  let β := pullback.snd (D.map j.hom) q ≫ 𝟙 P
  let α := pullback.snd (D.map j.hom) q
  letI : IsClosedImmersion (pullback.fst β t) := hj
  haveI : IsClosedImmersion (pullback.snd t β) := by
    have H : IsClosedImmersion ((pullbackSymmetry t β).hom ≫ pullback.fst β t) := inferInstance
    simpa only [pullbackSymmetry_hom_comp_fst] using H
  haveI : IsClosedImmersion (pullback.snd t α) :=
    isClosedImmersion_pullback_snd_of_composite t β (𝟙 _) α (by simp [β, α])
  haveI : IsClosedImmersion (pullback.fst α t) := by
    have H : IsClosedImmersion ((pullbackSymmetry α t).hom ≫ pullback.snd t α) := inferInstance
    simpa only [pullbackSymmetry_hom_comp_snd] using H
  haveI : IsProper (pullback.fst (D.map j.hom) f) :=
    isProper_pullback_fst_of_closed_domination f h t q hcomm (D.map j.hom)
  refine ⟨j.left, j.hom, ?_⟩
  have H : IsProper ((pullbackSymmetry f (D.map j.hom)).hom ≫
      pullback.fst (D.map j.hom) f) := inferInstance
  simpa only [pullbackSymmetry_hom_comp_fst] using H

end SerrePositivity.AlgebraicGeometry
