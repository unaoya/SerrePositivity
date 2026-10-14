module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerExact
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ConeShortExact
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.LocalizationTowerComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletionNaturality
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # 完備複体のKoszul冪塔からの標準再構成

恒等遷移の定数塔→Koszul剰余塔→シフトしたa倍遷移の塔の短完全列を使う。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 各Koszul剰余からシフトした元の複体への標準射影。 -/
def complexPowerKoszulProjection (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    complexPowerKoszulStage R a K n ⟶ K⟦(1 : ℤ)⟧ :=
  coneStandardProjection R (smulId (a ^ n) K)

/-- 各段の標準包含は、恒等遷移の塔からの射を与える。 -/
theorem complexPowerKoszulInclusion_towerMap (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    𝟙 K ≫ CochainComplex.mappingCone.inr (smulId (a ^ n) K) =
      CochainComplex.mappingCone.inr (smulId (a ^ (n + 1)) K) ≫
        complexPowerKoszulTransition R a K n := by
  simpa only [Category.id_comp] using (complexPowerKoszulInclusion_compatible R a K n).symm

/-- 標準射影は、a倍で結ぶシフト複体の塔への射を与える。 -/
theorem complexPowerKoszulProjection_towerMap (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    complexPowerKoszulTransition R a K n ≫ complexPowerKoszulProjection R a K n =
      complexPowerKoszulProjection R a K (n + 1) ≫ smulId a (K⟦(1 : ℤ)⟧) := by
  let α : Arrow.mk (smulId (a ^ (n + 1)) K) ⟶ Arrow.mk (smulId (a ^ n) K) :=
    Arrow.homMk (a • 𝟙 K) (𝟙 K) (by simp [smulId, smul_smul, pow_succ, mul_comm])
  change (cochainMappingConeFunctor R).map α ≫
    (CochainComplex.mappingCone.triangle (smulId (a ^ n) K)).mor₃ = _
  rw [cochainMappingConeFunctor_map_eq]
  have hh := (CochainComplex.mappingCone.triangleMap
    (smulId (a ^ (n + 1)) K) (smulId (a ^ n) K) α.left α.right α.w.symm).comm₃
  change complexPowerKoszulProjection R a K (n + 1) ≫ (a • 𝟙 K)⟦(1 : ℤ)⟧' =
    CochainComplex.mappingCone.map (smulId (a ^ (n + 1)) K) (smulId (a ^ n) K)
      α.left α.right α.w.symm ≫ complexPowerKoszulProjection R a K n at hh
  have hs : (a • 𝟙 K)⟦(1 : ℤ)⟧' = smulId a (K⟦(1 : ℤ)⟧) := by
    rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
    rfl
  rw [hs] at hh
  exact hh.symm

/-- 標準包含と標準射影の合成は零。 -/
theorem complexPowerKoszulInclusion_projection_zero (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    CochainComplex.mappingCone.inr (smulId (a ^ n) K) ≫
      complexPowerKoszulProjection R a K n = 0 :=
  (coneStandardShortComplex R (smulId (a ^ n) K)).zero

/-- 定数塔から完備化候補へのholimの標準射。 -/
def complexCompletionTowerInclusion (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    complexTowerHomotopyLimit R (constantComplexTower R K) (fun _ ↦ 𝟙 K) ⟶
      (complexCompletionFunctor R a).obj K :=
  complexTowerHomotopyLimitMap R
    (K := constantComplexTower R K) (L := complexPowerKoszulStage R a K)
    (fun _ ↦ 𝟙 K) (complexPowerKoszulTransition R a K)
    (fun n ↦ CochainComplex.mappingCone.inr (smulId (a ^ n) K))
    (complexPowerKoszulInclusion_towerMap R a K)

/-- 定数塔・Koszul剰余塔・シフトした残余塔を結ぶ標準短複体。 -/
def complexCompletionReconstructionSequence (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  complexTowerHomotopyLimitShortComplex R
    (K := constantComplexTower R K) (L := complexPowerKoszulStage R a K)
    (M := constantComplexTower R (K⟦(1 : ℤ)⟧)) (fun _ ↦ 𝟙 K)
    (complexPowerKoszulTransition R a K) (fun _ ↦ smulId a (K⟦(1 : ℤ)⟧))
    (fun n ↦ CochainComplex.mappingCone.inr (smulId (a ^ n) K))
    (complexPowerKoszulProjection R a K) (complexPowerKoszulInclusion_towerMap R a K)
    (complexPowerKoszulProjection_towerMap R a K)
    (complexPowerKoszulInclusion_projection_zero R a K)

/-- 三つの塔のholimの標準短複体は短完全。 -/
theorem complexCompletionReconstructionSequence_shortExact (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (complexCompletionReconstructionSequence R a K).ShortExact := by
  apply complexTowerHomotopyLimitShortComplex_shortExact
  intro n
  exact coneStandardShortComplex_shortExact R (smulId (a ^ n) K)

/-- 定数塔の対角射を経由した写像は、元の完備化の標準射と一致する。 -/
theorem constantComplexTowerUnit_comp_completionInclusion (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    constantComplexTowerUnit R K ≫ complexCompletionTowerInclusion R a K =
      complexCompletionUnit R a K := by
  apply complexTowerCompatibleLift_map
  intro n
  exact Category.id_comp _

/-- 完備対象では、再構成短完全列の最後の対象は実導来圏で零。 -/
theorem complexCompletionReconstructionSequence_third_isZero (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsComplete R a (DerivedCategory.Q.obj K)) :
    IsZero (DerivedCategory.Q.obj (complexCompletionReconstructionSequence R a K).X₃) := by
  apply scalarComplexTowerHomotopyLimitObject_isZero_of_isComplete R a (K⟦(1 : ℤ)⟧)
  exact isComplete_of_iso R a ((DerivedCategory.Q.commShiftIso (1 : ℤ)).symm.app K)
    (isComplete_shift R a hK 1)

/-- 完備対象では、定数塔のholimからKoszul完備化候補への標準射は導来同型。 -/
theorem complexCompletionTowerInclusion_isIso_of_isComplete (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsComplete R a (DerivedCategory.Q.obj K)) :
    IsIso (DerivedCategory.Q.map (complexCompletionTowerInclusion R a K)) := by
  let hS := complexCompletionReconstructionSequence_shortExact R a K
  exact (CategoryTheory.Pretriangulated.Triangle.isZero₃_iff_isIso₁
    (DerivedCategory.triangleOfSES hS) (DerivedCategory.triangleOfSES_distinguished hS)).mp
      (complexCompletionReconstructionSequence_third_isZero R a K hK)

/-- 完備複体は、そのKoszul冪剰余の塔のholimから標準射によって再構成される。 -/
theorem complexCompletionUnitObject_isIso_of_isComplete (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsComplete R a (DerivedCategory.Q.obj K)) :
    IsIso (complexCompletionUnitObject R a K) := by
  have := constantComplexTowerUnit_quasiIso R K
  have := complexCompletionTowerInclusion_isIso_of_isComplete R a K hK
  rw [complexCompletionUnitObject, ← constantComplexTowerUnit_comp_completionInclusion,
    CategoryTheory.Functor.map_comp]
  infer_instance

/-- 完備な代表複体に対する、標準射そのものの準同型同値。 -/
theorem complexCompletionUnit_quasiIso_of_isComplete (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsComplete R a (DerivedCategory.Q.obj K)) :
    QuasiIso (complexCompletionUnit R a K) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).mp
    (complexCompletionUnitObject_isIso_of_isComplete R a K hK)

/-- 完備な代表複体から、そのKoszul完備化への標準比較同型。 -/
def complexCompletionUnitIso (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsComplete R a (DerivedCategory.Q.obj K)) :
    DerivedCategory.Q.obj K ≅ complexCompletionObject R a K := by
  have := complexCompletionUnitObject_isIso_of_isComplete R a K hK
  exact asIso (complexCompletionUnitObject R a K)

/-- 実導来圏の任意の完備対象で、完備化の標準自然変換は同型である。 -/
theorem derivedComplexCompletionUnit_isIso_of_isComplete (a : R)
    (X : ConcreteDerivedCategory R) (hX : IsComplete R a X) :
    IsIso ((derivedComplexCompletionUnit R a).app X) := by
  let K := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  have hK : IsComplete R a (DerivedCategory.Q.obj K) := isComplete_of_iso R a e.symm hX
  have hunit := complexCompletionUnitObject_isIso_of_isComplete R a K hK
  have hQ : IsIso ((derivedComplexCompletionUnit R a).app (DerivedCategory.Q.obj K)) := by
    have : IsIso ((derivedComplexCompletionUnit R a).app (DerivedCategory.Q.obj K) ≫
        (derivedComplexCompletionComparison R a).hom.app K) := by
      rw [derivedComplexCompletionUnit_comparison]
      exact hunit
    exact IsIso.of_isIso_comp_right _ ((derivedComplexCompletionComparison R a).hom.app K)
  have hnat := (derivedComplexCompletionUnit R a).naturality e.hom
  change e.hom ≫ (derivedComplexCompletionUnit R a).app X =
    (derivedComplexCompletionUnit R a).app (DerivedCategory.Q.obj K) ≫
      (derivedComplexCompletionFunctor R a).map e.hom at hnat
  have : IsIso (e.hom ≫ (derivedComplexCompletionUnit R a).app X) := by
    rw [hnat]
    infer_instance
  exact IsIso.of_isIso_comp_left e.hom _

/-- 任意の完備導来対象の標準再構成同型。 -/
def derivedComplexCompletionUnitIso (a : R) (X : ConcreteDerivedCategory R)
    (hX : IsComplete R a X) : X ≅ (derivedComplexCompletionFunctor R a).obj X := by
  have := derivedComplexCompletionUnit_isIso_of_isComplete R a X hX
  exact asIso ((derivedComplexCompletionUnit R a).app X)

/-- 導来完備性は、完備化の標準射が同型となることと同値。 -/
theorem isComplete_iff_derivedComplexCompletionUnit_isIso (a : R)
    (X : ConcreteDerivedCategory R) :
    IsComplete R a X ↔ IsIso ((derivedComplexCompletionUnit R a).app X) := by
  constructor
  · exact derivedComplexCompletionUnit_isIso_of_isComplete R a X
  · intro h
    exact isComplete_of_iso R a (asIso ((derivedComplexCompletionUnit R a).app X)).symm
      (derivedComplexCompletionFunctor_isComplete R a X)

end SerrePositivity.DerivedCompletion
