module

public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaPDivisionSequentialKoszulAugmentation

/-! # 実無限Koszul比較の標準単位

圏論的colimitへの標準射を追い、H⁰比較を元の自由環の標準商射で正規化する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "g₀" => deltaDivisionIteratedRelation D (p : A) a₀ (default : σ)
local notation "F₀" => deltaPDivisionFiniteKoszulDiagram (σ := σ) D y

/-- 実ホモロジー極限比較は、各有限Koszul段からの実標準射を保つ。 -/
theorem deltaPDivisionSequentialKoszulHomologyColimitIso_ι (i : ℤ) (N : ℕ) :
    homologyMap (colimit.ι F₀ N) i ≫
      (deltaPDivisionSequentialKoszulHomologyColimitIso D y i).hom =
        colimit.ι (F₀ ⋙ homologyFunctor (ModuleCat.{u} L₀) (.up ℤ) i) N := by
  haveI : AB5OfSize.{0, 0} (ModuleCat.{u} L₀) := AB5OfSize_of_univLE (ModuleCat.{u} L₀)
  let K := deltaPDivisionSequentialKoszulDiagramComplex (σ := σ) D y
  let τ : (evaluation ℕ (ModuleCat.{u} L₀)).obj N ⟶
      (colim : (ℕ ⥤ ModuleCat.{u} L₀) ⥤ ModuleCat.{u} L₀) :=
    { app := fun U => colimit.ι U N
      naturality := fun U V f => (colimit.ι_map f N).symm }
  have h := CategoryTheory.ShortComplex.homologyMap_mapNatTrans (K.sc i) τ
  change homologyMap ((coconeOfHasColimitEval F₀).ι.app N) i =
    ((K.sc i).mapHomologyIso ((evaluation ℕ (ModuleCat.{u} L₀)).obj N)).hom ≫
      colimit.ι (K.homology i) N ≫
      ((K.sc i).mapHomologyIso (colim : (ℕ ⥤ ModuleCat.{u} L₀) ⥤ ModuleCat.{u} L₀)).inv at h
  dsimp only [K] at h
  have hc : colimit.ι F₀ N ≫
      (deltaPDivisionSequentialKoszulTermwiseColimitIso D y).inv =
        (coconeOfHasColimitEval F₀).ι.app N :=
    IsColimit.comp_coconePointUniqueUpToIso_inv
      (isColimitCoconeOfHasColimitEval F₀) (colimit.isColimit F₀) N
  simp only [deltaPDivisionSequentialKoszulHomologyColimitIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, homologyFunctor_map]
  rw [← homologyMap_comp_assoc, hc, h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [colimit.ι_map]
  change ((K.sc i).mapHomologyIso ((evaluation ℕ (ModuleCat.{u} L₀)).obj N)).hom ≫
    ((K.sc i).mapHomologyIso ((evaluation ℕ (ModuleCat.{u} L₀)).obj N)).inv ≫ _ = _
  simp only [Iso.hom_inv_id_assoc]

/-- 実H⁰極限比較は、通常有限商の標準遷移図式への比較とも両立する。 -/
theorem deltaPDivisionSequentialKoszulH0ColimitIso_ι (N : ℕ) :
    homologyMap (colimit.ι F₀ N) 0 ≫ (deltaPDivisionSequentialKoszulH0ColimitIso D y).hom =
      (deltaPDivisionFiniteKoszulH0Equiv D y N).toModuleIso.hom ≫
        colimit.ι (deltaPDivisionFiniteQuotientModuleDiagram D y) N := by
  rw [deltaPDivisionSequentialKoszulH0ColimitIso, Iso.trans_hom, Functor.mapIso_hom,
    ← Category.assoc, deltaPDivisionSequentialKoszulHomologyColimitIso_ι,
    colimit.ι_map, deltaPDivisionFiniteKoszulH0DiagramIso_app]

/-- 実H⁰とraw δ包の比較は、有限段の実H⁰比較とraw標準射を保つ。 -/
theorem deltaPDivisionSequentialKoszulH0RawIso_ι (N : ℕ) :
    homologyMap (colimit.ι F₀ N) 0 ≫ (deltaPDivisionSequentialKoszulH0RawIso D y).hom =
      (deltaPDivisionFiniteKoszulH0Equiv D y N).toModuleIso.hom ≫
        ModuleCat.ofHom (deltaPDivisionFiniteQuotientToRaw D y N) := by
  rw [deltaPDivisionSequentialKoszulH0RawIso, Iso.trans_hom, ← Category.assoc,
    deltaPDivisionSequentialKoszulH0ColimitIso_ι, Category.assoc,
    deltaPDivisionFiniteQuotientColimitRawIso_ι]

/-- 任意有限段の標準単位を実極限へ送ると、raw比較は元の標準商元を与える。 -/
theorem deltaPDivisionSequentialKoszulH0RawIso_unit (N : ℕ) (r : L₀) :
    (deltaPDivisionSequentialKoszulH0RawIso D y).hom.hom
      ((homologyMap (colimit.ι F₀ N) 0).hom
        (SerrePositivity.DerivedCompletion.koszulH0Unit L₀
          (fun j : Fin (N + 1) => g₀ j.val) r)) =
      Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
        (deltaDivisionRelationIdeal (p : A) a₀)) r := by
  have h := congrArg (fun f => f.hom (SerrePositivity.DerivedCompletion.koszulH0Unit L₀
    (fun j : Fin (N + 1) => g₀ j.val) r)) (deltaPDivisionSequentialKoszulH0RawIso_ι D y N)
  change (deltaPDivisionSequentialKoszulH0RawIso D y).hom.hom
      ((homologyMap (colimit.ι F₀ N) 0).hom
        (SerrePositivity.DerivedCompletion.koszulH0Unit L₀
          (fun j : Fin (N + 1) => g₀ j.val) r)) =
    deltaPDivisionFiniteQuotientToRaw D y N
      (deltaPDivisionFiniteKoszulH0Equiv D y N
        (SerrePositivity.DerivedCompletion.koszulH0Unit L₀
          (fun j : Fin (N + 1) => g₀ j.val) r)) at h
  rw [deltaPDivisionFiniteKoszulH0Equiv_unit, deltaPDivisionFiniteQuotientToRaw_mk] at h
  exact h

/-- 実無限添加写像のH⁰も、各有限段の標準単位をraw標準商元へ送る。 -/
theorem deltaPDivisionSequentialKoszulAugmentation_homology_unit (N : ℕ) (r : L₀) :
    (homologyMap (deltaPDivisionSequentialKoszulAugmentation D y) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
        (ModuleCat.of L₀ (DeltaAdjoinDivision D (p : A) a₀))).hom).hom
      ((homologyMap (colimit.ι F₀ N) 0).hom
        (SerrePositivity.DerivedCompletion.koszulH0Unit L₀
          (fun j : Fin (N + 1) => g₀ j.val) r)) =
      Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
        (deltaDivisionRelationIdeal (p : A) a₀)) r := by
  rw [deltaPDivisionSequentialKoszulAugmentation_homologyMap]
  exact deltaPDivisionSequentialKoszulH0RawIso_unit D y N r

end SerrePositivity.BhattScholze
