module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PairKoszulCone
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.Maps
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalKoszulUnit

/-! # 二座標Koszul完備化の標準写像と行列モデルの定数サイクル -/

@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open HomologicalComplex.homotopyCofiber
variable (R : Type u) [CommRing R]

/-- 具体的な有限段への標準包含。 -/
def pairKoszulStageInclusion (f d : R) (n : ℕ) :
    principalSingle R ⟶ pairKoszulTower R f d n :=
  koszulComplexInclusion R (fun _ : Fin 1 ↦ f ^ n) ≫
    CochainComplex.mappingCone.inr (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n))

/-- 有限段の表示同型は標準包含を保つ。 -/
theorem pairKoszulStageInclusion_naturality (f d : R) (n : ℕ) :
    koszulComplexInclusion R (fun i ↦ pairKoszulCoordinates R f d i ^ n) ≫
      (pairKoszulStageIso R f d n).hom = pairKoszulStageInclusion R f d n := by
  simp only [pairKoszulStageIso, pairKoszulTower, powerKoszulTower, koszulComplex_succ,
    eqToIso_refl, Iso.refl_hom, Category.comp_id]
  simp only [pairKoszulStageInclusion, koszulComplexInclusion, pairKoszulCoordinates]
  rfl

/-- 具体的な有限段の零次数成分は、標準包含の元を保つ。 -/
theorem pairKoszulStageInclusion_zero (f d : R) (n : ℕ) (r : R) :
    pairKoszulStageZeroEquiv R f d n ((pairKoszulStageInclusion R f d n).f 0
      ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r)) = r := by
  rw [pairKoszulStageZeroEquiv_apply]
  change (principalKoszulStageZeroIso R f n).hom
    (sndX (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n)) 0
      (inrX (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n)) 0
        ((koszulComplexInclusion R (fun _ : Fin 1 ↦ f ^ n)).f 0
          ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r)))) = r
  rw [moduleCone_snd_inr_apply]
  exact congrArg (fun g ↦ g.hom r) (principalKoszulInclusion_zero R f n)

/-- 元の標準写像を、具体的な塔表示へ運ぶ。 -/
def pairKoszulCompletionUnit (f d : R) :
    principalSingle R ⟶ pairKoszulCompletionComplex R f d :=
  koszulCompletionUnit R (pairKoszulCoordinates R f d) ≫ (pairKoszulCompletionIso R f d).hom

/-- 運んだ標準写像の第1射影を、各段の標準包含で計算する。 -/
theorem pairKoszulCompletionUnit_fst_projection (f d : R) (n : ℕ) :
    (pairKoszulCompletionUnit R f d).f 0 ≫ fstX (pairKoszulDifference R f d) (-1) 0 (by decide) ≫
      (Pi.π (pairKoszulTower R f d) n).f 0 = (pairKoszulStageInclusion R f d n).f 0 := by
  have he := complexTowerHomotopyLimitIso_fst_zero R
    (powerKoszulTransition R (pairKoszulCoordinates R f d)) (pairKoszulTransition R f d)
    (pairKoszulStageIso R f d) (fun n ↦ (pairKoszulStageIso_naturality R f d n).symm)
  change (pairKoszulCompletionIso R f d).hom.f 0 ≫
    fstX (pairKoszulDifference R f d) (-1) 0 (by decide) =
      fstX (complexTowerDifference R (powerKoszulTower R (pairKoszulCoordinates R f d))
        (powerKoszulTransition R (pairKoszulCoordinates R f d))) (-1) 0 (by decide) ≫
      (complexTowerProductIso R (pairKoszulStageIso R f d)).hom.f 0 at he
  have hp := congrArg (fun g ↦ g.f 0)
    (complexTowerProductMap_projection R (fun n ↦ (pairKoszulStageIso R f d n).hom) n)
  have hu := congrArg (fun g ↦ g.f 0)
    (koszulCompletionUnit_comp_projection R (pairKoszulCoordinates R f d) n)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    complexTowerProjection_fst_zero] at hu
  change (koszulCompletionUnit R (pairKoszulCoordinates R f d)).f 0 ≫
    fstX (complexTowerDifference R (powerKoszulTower R (pairKoszulCoordinates R f d))
      (powerKoszulTransition R (pairKoszulCoordinates R f d))) (-1) 0 (by decide) ≫
    (Pi.π (powerKoszulTower R (pairKoszulCoordinates R f d)) n).f 0 =
      (koszulComplexInclusion R (fun i ↦ pairKoszulCoordinates R f d i ^ n)).f 0 at hu
  have hi := congrArg (fun g ↦ g.f 0) (pairKoszulStageInclusion_naturality R f d n)
  change (koszulComplexInclusion R (fun i ↦ pairKoszulCoordinates R f d i ^ n)).f 0 ≫
    (pairKoszulStageIso R f d n).hom.f 0 = (pairKoszulStageInclusion R f d n).f 0 at hi
  let u := (koszulCompletionUnit R (pairKoszulCoordinates R f d)).f 0
  let F := fstX (complexTowerDifference R (powerKoszulTower R (pairKoszulCoordinates R f d))
    (powerKoszulTransition R (pairKoszulCoordinates R f d))) (-1) 0 (by decide)
  let G := fstX (pairKoszulDifference R f d) (-1) 0 (by decide)
  let a := (complexTowerProductIso R (pairKoszulStageIso R f d)).hom.f 0
  let pK := (Pi.π (powerKoszulTower R (pairKoszulCoordinates R f d)) n).f 0
  let pL := (Pi.π (pairKoszulTower R f d) n).f 0
  let q := (pairKoszulStageIso R f d n).hom.f 0
  have hp' : a ≫ pL = pK ≫ q := hp
  change u ≫ (pairKoszulCompletionIso R f d).hom.f 0 ≫ G ≫ pL = _
  calc
    u ≫ (pairKoszulCompletionIso R f d).hom.f 0 ≫ G ≫ pL =
        u ≫ ((pairKoszulCompletionIso R f d).hom.f 0 ≫ G) ≫ pL := by
          simp only [Category.assoc]
    _ = u ≫ (F ≫ a) ≫ pL := by rw [he]
    _ = (u ≫ F ≫ pK) ≫ q := by
      simp only [Category.assoc]
      rw [hp']
    _ = (pairKoszulStageInclusion R f d n).f 0 := by rw [hu, hi]

/-- 表示同型を通して運んだ標準写像の第2成分は零。 -/
theorem pairKoszulCompletionUnit_snd_zero (f d : R) :
    (pairKoszulCompletionUnit R f d).f 0 ≫ sndX (pairKoszulDifference R f d) (-1) = 0 := by
  have he := complexTowerHomotopyLimitIso_snd_zero R
    (powerKoszulTransition R (pairKoszulCoordinates R f d)) (pairKoszulTransition R f d)
    (pairKoszulStageIso R f d) (fun n ↦ (pairKoszulStageIso_naturality R f d n).symm)
  let u := (koszulCompletionUnit R (pairKoszulCoordinates R f d)).f 0
  let F := sndX (complexTowerDifference R (powerKoszulTower R (pairKoszulCoordinates R f d))
    (powerKoszulTransition R (pairKoszulCoordinates R f d))) (-1)
  let G := sndX (pairKoszulDifference R f d) (-1)
  let a := (complexTowerProductIso R (pairKoszulStageIso R f d)).hom.f (-1)
  have hu : u ≫ F = 0 := by
    dsimp only [u, F, koszulCompletionUnit, complexTowerCompatibleLift]
    apply complexTowerHomotopyLimitLift_snd_component
  change u ≫ (pairKoszulCompletionIso R f d).hom.f 0 ≫ G = 0
  change (pairKoszulCompletionIso R f d).hom.f 0 ≫ G = F ≫ a at he
  calc
    u ≫ (pairKoszulCompletionIso R f d).hom.f 0 ≫ G =
        u ≫ ((pairKoszulCompletionIso R f d).hom.f 0 ≫ G) := rfl
    _ = (u ≫ F) ≫ a := by rw [he]; simp only [Category.assoc]
    _ = 0 := by rw [hu, CategoryTheory.Limits.zero_comp]

/-- 標準写像の第一列は定数列。 -/
theorem pairCompletionZeroEquiv_unit_fst (f d r : R) :
    (pairCompletionZeroEquiv R f d ((pairKoszulCompletionUnit R f d).f 0
      ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r))).1 = fun _ ↦ r := by
  funext n
  rw [pairCompletionZeroEquiv_fst, pairKoszulProductZeroEquiv_apply,
    complexProductDegreeEquiv_apply]
  have h := congrArg (fun g ↦ g.hom
    ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r))
      (pairKoszulCompletionUnit_fst_projection R f d n)
  change (Pi.π (pairKoszulTower R f d) n).f 0
    (fstX (pairKoszulDifference R f d) (-1) 0 (by decide)
      ((pairKoszulCompletionUnit R f d).f 0
        ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r))) =
      (pairKoszulStageInclusion R f d n).f 0
        ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r) at h
  rw [h, pairKoszulStageInclusion_zero]

/-- 標準写像の二つの補助列は零。 -/
theorem pairCompletionZeroEquiv_unit_snd (f d r : R) :
    (pairCompletionZeroEquiv R f d ((pairKoszulCompletionUnit R f d).f 0
      ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r))).2 = 0 := by
  rw [pairCompletionZeroEquiv_snd]
  have h := congrArg (fun g ↦ g.hom
    ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r))
      (pairKoszulCompletionUnit_snd_zero R f d)
  change sndX (pairKoszulDifference R f d) (-1) ((pairKoszulCompletionUnit R f d).f 0
    ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r)) = 0 at h
  rw [h, map_zero, neg_zero]

/-- 元の標準写像は、行列表示では定数列と二つの零列になる。 -/
theorem pairCompletionZeroEquiv_unit (f d r : R) :
    pairCompletionZeroEquiv R f d ((pairKoszulCompletionUnit R f d).f 0
      ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r)) =
      (fun _ ↦ r, (0, 0)) :=
  Prod.ext (pairCompletionZeroEquiv_unit_fst R f d r) (pairCompletionZeroEquiv_unit_snd R f d r)

/-- 元の標準写像を、行列モデルの短複体へ移した写像。 -/
def pairCompletionUnitShortMap (f d : R) :
    (principalSingle R).sc 0 ⟶ pairTowerShortComplex R f d :=
  (HomologicalComplex.shortComplexFunctor _ _ 0).map
    (koszulCompletionUnit R (pairKoszulCoordinates R f d)) ≫
      (pairKoszulCompletionShortComplexIso R f d).hom

/-- 標準短複体写像は、標準サイクルを保つ。 -/
theorem pairCompletionUnitShortMap_cycles (f d r : R) :
    ShortComplex.cyclesMap (pairCompletionUnitShortMap R f d)
      ((HomologicalComplex.singleObjCyclesSelfIso _ 0 (ModuleCat.of R R)).inv r) =
      (pairTowerShortComplex R f d).moduleCatCyclesIso.inv
        (pairTowerConstantCycle R f d r) := by
  apply (ModuleCat.mono_iff_injective (pairTowerShortComplex R f d).iCycles).mp inferInstance
  have h := congrArg (fun g ↦ g.hom
    ((HomologicalComplex.singleObjCyclesSelfIso _ 0 (ModuleCat.of R R)).inv r))
      (ShortComplex.cyclesMap_i (pairCompletionUnitShortMap R f d))
  change (pairTowerShortComplex R f d).iCycles
    (ShortComplex.cyclesMap (pairCompletionUnitShortMap R f d)
      ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0
        (ModuleCat.of R R)).inv r)) = (pairCompletionUnitShortMap R f d).τ₂
      ((principalSingle R).iCycles 0
        ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0
          (ModuleCat.of R R)).inv r)) at h
  rw [h]
  have hsrc := congrArg (fun g ↦ g.hom r)
    (HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles
      (ComplexShape.up ℤ) 0 (ModuleCat.of R R))
  change (principalSingle R).iCycles 0
    ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0
      (ModuleCat.of R R)).inv r) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R R)).inv r at hsrc
  have htgt := congrArg (fun g ↦ g.hom (pairTowerConstantCycle R f d r))
    (pairTowerShortComplex R f d).moduleCatCyclesIso_inv_iCycles
  change (pairTowerShortComplex R f d).iCycles
    ((pairTowerShortComplex R f d).moduleCatCyclesIso.inv (pairTowerConstantCycle R f d r)) =
      (pairTowerConstantCycle R f d r).val at htgt
  rw [htgt]
  change (pairCompletionUnitShortMap R f d).τ₂
    ((principalSingle R).iCycles 0
      ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0
        (ModuleCat.of R R)).inv r)) = _
  rw [hsrc]
  change pairCompletionZeroEquiv R f d ((pairKoszulCompletionUnit R f d).f 0
    ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r)) = _
  rw [pairCompletionZeroEquiv_unit, pairTowerConstantCycle_val]

/-- 実際のH⁰の同型は、既存の標準写像をモデルの標準写像へ送る。 -/
theorem pairKoszulCompletionH0Equiv_unit (f d r : R) :
    pairKoszulCompletionH0Equiv R f d
      (koszulCompletionH0Unit R (pairKoszulCoordinates R f d) r) =
        pairTowerHomologyUnit R f d r := by
  let c : (principalSingle R).cycles 0 :=
    (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 (ModuleCat.of R R)).inv r
  have hrep : (HomologicalComplex.singleObjHomologySelfIso _ 0 (ModuleCat.of R R)).inv r =
      (principalSingle R).homologyπ 0 c := by
    have h : (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
        (ModuleCat.of R R)).inv =
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0
        (ModuleCat.of R R)).inv ≫ (principalSingle R).homologyπ 0 := by
      rw [← HomologicalComplex.singleObjHomologySelfIso_hom_singleObjHomologySelfIso_inv]
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    exact congrArg (fun g ↦ g.hom r) h
  have hn := congrArg (fun g ↦ g.hom c)
    (ShortComplex.homologyπ_naturality (pairCompletionUnitShortMap R f d))
  change ShortComplex.homologyMap (pairCompletionUnitShortMap R f d)
    ((principalSingle R).homologyπ 0 c) = (pairTowerShortComplex R f d).homologyπ
      (ShortComplex.cyclesMap (pairCompletionUnitShortMap R f d) c) at hn
  rw [show ShortComplex.cyclesMap (pairCompletionUnitShortMap R f d) c =
    (pairTowerShortComplex R f d).moduleCatCyclesIso.inv (pairTowerConstantCycle R f d r)
      from pairCompletionUnitShortMap_cycles R f d r] at hn
  change ShortComplex.homologyMap (pairKoszulCompletionShortComplexIso R f d).hom
    (HomologicalComplex.homologyMap (koszulCompletionUnit R (pairKoszulCoordinates R f d)) 0
      ((HomologicalComplex.singleObjHomologySelfIso _ 0 (ModuleCat.of R R)).inv r)) = _
  rw [hrep]
  have hcomp : ShortComplex.homologyMap (pairCompletionUnitShortMap R f d) =
      HomologicalComplex.homologyMap (koszulCompletionUnit R (pairKoszulCoordinates R f d)) 0 ≫
        ShortComplex.homologyMap (pairKoszulCompletionShortComplexIso R f d).hom :=
    ShortComplex.homologyMap_comp _ _
  rw [hcomp] at hn
  exact hn

end SerrePositivity.DerivedCompletion
