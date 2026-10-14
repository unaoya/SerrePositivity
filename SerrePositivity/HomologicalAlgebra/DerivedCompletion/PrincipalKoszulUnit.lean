module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalKoszulCone
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.KoszulUnitCompatibility

/-! # 一座標Koszul完備化の標準写像の具体的な座標

実際のmapping coneへの持ち上げと、三項モデルの定数サイクルを比較する。
-/

@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
open HomologicalComplex.homotopyCofiber
variable (R : Type u) [CommRing R]

/-- Koszulの標準包含は、零次数の成分同型を通じて元の元へ戻る。 -/
theorem principalKoszulInclusion_zero (f : R) (n : ℕ) :
    (HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv ≫
      (koszulComplexInclusion R (fun _ : Fin 1 ↦ f ^ n)).f 0 ≫
        (principalKoszulStageZeroIso R f n).hom = 𝟙 (ModuleCat.of R R) := by
  simp [koszulComplexInclusion, principalKoszulStageZeroIso_hom, koszulComplex,
    CochainComplex.mappingCone.inr, HomologicalComplex.homotopyCofiber.inr_f]

/-- ホモトピー逆極限への標準持ち上げの第2成分は、各次数で零。 -/
theorem complexTowerHomotopyLimitLift_snd_component
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (g : P ⟶ piObj K)
    (hg : g ≫ complexTowerDifference R K t = 0) (i : ℤ) :
    (complexTowerHomotopyLimitLift R K t P g hg).f i ≫
      sndX (complexTowerDifference R K t) (i + -1) = 0 := by
  have h := congrArg (fun γ ↦ γ.v i (i + -1) rfl)
    (complexTowerHomotopyLimitLift_snd R K t P g hg)
  simp only [CochainComplex.HomComplex.Cochain.comp_v
    (n₁ := -1) (n₂ := 0) (n₁₂ := -1) _ _ _ i (i + -1) (i + -1) rfl (by omega)] at h
  change ((CochainComplex.HomComplex.Cochain.ofHom
    (complexTowerHomotopyLimitLift R K t P g hg)).rightUnshift (-1) (zero_add _)).v
      i (i + -1) rfl ≫
        (CochainComplex.mappingCone.snd (complexTowerDifference R K t)).v
          (i + -1) (i + -1) (add_zero _) = 0 at h
  rw [CochainComplex.HomComplex.Cochain.rightUnshift_v _ _ _ i (i + -1) rfl
    i (add_zero i)] at h
  simpa [CochainComplex.mappingCone.snd, CochainComplex.shiftFunctorObjXIso] using h

/-- 正規化されたホモトピー逆極限射影の零次数成分。 -/
theorem principalCompletionProjection_zero (f : R) :
    (complexTowerProjection R (powerKoszulTower R (fun _ : Fin 1 ↦ f))
      (powerKoszulTransition R (fun _ : Fin 1 ↦ f))).f 0 =
    fstX (principalKoszulDifference R f) (-1) 0 (by decide) := by
  simp [complexTowerProjection, CochainComplex.mappingCocone.fst,
    CochainComplex.HomComplex.Cochain.leftShift, CochainComplex.shiftFunctorObjXIso,
    CochainComplex.mappingCone.fst]

/-- 一座標完備化の標準写像の第1座標は定数列。 -/
theorem principalCompletionZeroEquiv_unit_fst (f r : R) :
    (principalCompletionZeroEquiv R f
      ((koszulCompletionUnit R (fun _ : Fin 1 ↦ f)).f 0
        ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r))).1 =
      fun _ ↦ r := by
  ext n
  rw [principalCompletionZeroEquiv_fst, principalKoszulProductZeroEquiv_apply]
  have h := congrArg (fun g ↦ (g.f 0).hom
    ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r))
      (koszulCompletionUnit_comp_projection R (fun _ : Fin 1 ↦ f) n)
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply,
    principalCompletionProjection_zero] at h
  change (Pi.π (powerKoszulTower R (fun _ : Fin 1 ↦ f)) n).f 0
    (fstX (principalKoszulDifference R f) (-1) 0 (by decide)
      ((koszulCompletionUnit R (fun _ : Fin 1 ↦ f)).f 0
        ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r))) =
      (koszulComplexInclusion R (fun _ : Fin 1 ↦ f ^ n)).f 0
        ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r) at h
  rw [h]
  exact congrArg (fun g ↦ g.hom r) (principalKoszulInclusion_zero R f n)

/-- 一座標完備化の標準写像の第2座標は零。 -/
theorem principalCompletionZeroEquiv_unit_snd (f r : R) :
    (principalCompletionZeroEquiv R f
      ((koszulCompletionUnit R (fun _ : Fin 1 ↦ f)).f 0
        ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r))).2 = 0 := by
  rw [principalCompletionZeroEquiv_snd]
  have h : (koszulCompletionUnit R (fun _ : Fin 1 ↦ f)).f 0 ≫
      sndX (principalKoszulDifference R f) (-1) = 0 := by
    dsimp only [koszulCompletionUnit, complexTowerCompatibleLift]
    apply complexTowerHomotopyLimitLift_snd_component
  have hr := congrArg (fun g ↦ g.hom
    ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r)) h
  change sndX (principalKoszulDifference R f) (-1)
    ((koszulCompletionUnit R (fun _ : Fin 1 ↦ f)).f 0
      ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r)) = 0 at hr
  rw [hr, map_zero, neg_zero]

/-- 標準包含は定数列と零列の組へ送られる。 -/
theorem principalCompletionZeroEquiv_unit (f r : R) :
    principalCompletionZeroEquiv R f
      ((koszulCompletionUnit R (fun _ : Fin 1 ↦ f)).f 0
        ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r)) =
      (fun _ ↦ r, 0) :=
  Prod.ext (principalCompletionZeroEquiv_unit_fst R f r)
    (principalCompletionZeroEquiv_unit_snd R f r)

/-- 短複体同型の中項は、正規化した列の組の座標写像。 -/
theorem principalCompletionShortComplexIso_hom_τ₂ (f : R) :
    (principalCompletionShortComplexIso R f).hom.τ₂ =
      (principalCompletionZeroEquiv R f).toModuleIso.hom := rfl

/-- 単一複体から三項モデルへの標準短複体写像。 -/
def principalCompletionUnitShortMap (f : R) :
    (principalSingle R).sc 0 ⟶ principalTowerShortComplex R f :=
  (HomologicalComplex.shortComplexFunctor _ _ 0).map
    (koszulCompletionUnit R (fun _ : Fin 1 ↦ f)) ≫
      (principalCompletionShortComplexIso R f).hom

/-- 標準短複体写像は、サイクルとしての標準元も保つ。 -/
theorem principalCompletionUnitShortMap_cycles (f r : R) :
    ShortComplex.cyclesMap (principalCompletionUnitShortMap R f)
      ((HomologicalComplex.singleObjCyclesSelfIso _ 0 (ModuleCat.of R R)).inv r) =
    (principalTowerShortComplex R f).moduleCatCyclesIso.inv
      (principalTowerConstantCycle R f r) := by
  apply (ModuleCat.mono_iff_injective (principalTowerShortComplex R f).iCycles).mp
    inferInstance
  have h := congrArg (fun g ↦ g.hom
    ((HomologicalComplex.singleObjCyclesSelfIso _ 0 (ModuleCat.of R R)).inv r))
      (ShortComplex.cyclesMap_i (principalCompletionUnitShortMap R f))
  change (principalTowerShortComplex R f).iCycles
    (ShortComplex.cyclesMap (principalCompletionUnitShortMap R f)
      ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0
        (ModuleCat.of R R)).inv r)) =
      (principalCompletionUnitShortMap R f).τ₂
        ((principalSingle R).iCycles 0
          ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0
            (ModuleCat.of R R)).inv r)) at h
  rw [h]
  have hsrc := congrArg (fun g ↦ g.hom r)
    (HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles
      (ComplexShape.up ℤ) 0 (ModuleCat.of R R))
  have htgt := congrArg (fun g ↦ g.hom (principalTowerConstantCycle R f r))
    (principalTowerShortComplex R f).moduleCatCyclesIso_inv_iCycles
  change (principalTowerShortComplex R f).iCycles
    ((principalTowerShortComplex R f).moduleCatCyclesIso.inv
      (principalTowerConstantCycle R f r)) = (principalTowerConstantCycle R f r).val at htgt
  rw [htgt]
  change (principalSingle R).iCycles 0
    ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0
      (ModuleCat.of R R)).inv r) =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R R)).inv r at hsrc
  change (principalCompletionUnitShortMap R f).τ₂
    ((principalSingle R).iCycles 0
      ((HomologicalComplex.singleObjCyclesSelfIso _ 0 (ModuleCat.of R R)).inv r)) = _
  rw [hsrc]
  change principalCompletionZeroEquiv R f
    ((koszulCompletionUnit R (fun _ : Fin 1 ↦ f)).f 0
      ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r)) = _
  rw [principalCompletionZeroEquiv_unit, principalTowerConstantCycle_val]

/-- H⁰の比較同型は、既存の標準写像を列の商の標準写像へ送る。 -/
theorem principalCompletionH0Equiv_unit (f r : R) :
    principalCompletionH0Equiv R f
      (koszulCompletionH0Unit R (fun _ : Fin 1 ↦ f) r) =
    principalReflectionMk R f (sequenceHead R r) := by
  let c : (principalSingle R).cycles 0 :=
    (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 (ModuleCat.of R R)).inv r
  have hrep : (HomologicalComplex.singleObjHomologySelfIso _ 0
      (ModuleCat.of R R)).inv r = (principalSingle R).homologyπ 0 c := by
    have h : (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
        (ModuleCat.of R R)).inv =
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0
        (ModuleCat.of R R)).inv ≫ (principalSingle R).homologyπ 0 := by
      rw [← HomologicalComplex.singleObjHomologySelfIso_hom_singleObjHomologySelfIso_inv]
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    exact congrArg (fun g ↦ g.hom r) h
  have hn := congrArg (fun g ↦ g.hom c)
    (ShortComplex.homologyπ_naturality (principalCompletionUnitShortMap R f))
  change ShortComplex.homologyMap (principalCompletionUnitShortMap R f)
    ((principalSingle R).homologyπ 0 c) =
      (principalTowerShortComplex R f).homologyπ
        (ShortComplex.cyclesMap (principalCompletionUnitShortMap R f) c) at hn
  rw [show ShortComplex.cyclesMap (principalCompletionUnitShortMap R f) c =
    (principalTowerShortComplex R f).moduleCatCyclesIso.inv
      (principalTowerConstantCycle R f r) from principalCompletionUnitShortMap_cycles R f r] at hn
  change principalTowerHomologyEquiv R f
    (ShortComplex.homologyMap (principalCompletionShortComplexIso R f).hom
      (HomologicalComplex.homologyMap (koszulCompletionUnit R (fun _ : Fin 1 ↦ f)) 0
        ((HomologicalComplex.singleObjHomologySelfIso _ 0 (ModuleCat.of R R)).inv r))) = _
  rw [hrep]
  have hcomp : ShortComplex.homologyMap (principalCompletionUnitShortMap R f) =
      HomologicalComplex.homologyMap (koszulCompletionUnit R (fun _ : Fin 1 ↦ f)) 0 ≫
        ShortComplex.homologyMap (principalCompletionShortComplexIso R f).hom :=
    ShortComplex.homologyMap_comp _ _
  rw [hcomp] at hn
  change ShortComplex.homologyMap (principalCompletionShortComplexIso R f).hom
    (HomologicalComplex.homologyMap (koszulCompletionUnit R (fun _ : Fin 1 ↦ f)) 0
      ((principalSingle R).homologyπ 0 c)) = principalTowerHomologyUnit R f r at hn
  rw [hn, principalTowerHomologyEquiv_unit]

/-- 実際の一座標Koszul完備化のH⁰は、標準元について完備加群への反射。 -/
theorem principalCompletionH0_isCompleteModuleReflection (f : R) :
    IsCompleteModuleReflection R (fun _ : Fin 1 ↦ f)
      ((koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).homology 0)
      (koszulCompletionH0Unit R (fun _ : Fin 1 ↦ f) 1) :=
  (principalReflection_isCompleteModuleReflection R f).of_linearEquiv R
    (principalCompletionH0Equiv R f).symm (by
      apply (principalCompletionH0Equiv R f).injective
      rw [LinearEquiv.apply_symm_apply, principalCompletionH0Equiv_unit]
      rfl)

end SerrePositivity.DerivedCompletion
