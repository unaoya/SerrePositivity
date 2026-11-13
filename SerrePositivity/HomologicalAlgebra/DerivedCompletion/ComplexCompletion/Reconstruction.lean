module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.Maps
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ConeAPI
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Localization
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletion.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Closure
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.Milnor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Complete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Reflection
public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES

/-! # 完備複体の再構成と完備化のホモロジー

## 概要

恒等遷移の定数塔 → Koszul の剰余の塔 → `a` 倍遷移の塔の短完全列から、完備な複体を Koszul 冪塔から標準的に再構成する。完備化の候補のホモロジーが導来完備加群であること（Milnor 列と閉性による）、任意の導来完備対象のホモロジーが完備であること、項が導来完備な複体は導来完備であることを示す。

## 方針

有限段のホモロジーの完備性を、直積・核・余核・拡大の閉性と Milnor 列で候補の全次数へ移す。lim¹ を消す必要はない。

## 規約

旧 `ComplexCompletionReconstruction`・`TowerHomologyComplete`・`ComplexCompletionHomologyComplete`・`TermwiseComplete`。

## 使われ方

`CompletionReflection`、BhattScholze。
-/

@[expose] public noncomputable section

universe u

section ComplexCompletionReconstructionPart

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

end ComplexCompletionReconstructionPart

section TowerHomologyCompletePart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- 二つの隣接次数の有限段ホモロジーが完備なら、ホモトピー逆極限の同じ次数も完備。 -/
theorem complexTowerHomology_isModuleComplete_of_stages (f : R)
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n) (i : ℤ)
    (hprev : ∀ n, IsModuleComplete R f ((K n).homology (i - 1)))
    (hsame : ∀ n, IsModuleComplete R f ((K n).homology i)) :
    IsModuleComplete R f ((complexTowerHomotopyLimit R K t).homology i) := by
  have hp := isModuleComplete_pi R f (fun n ↦ (K n).homology (i - 1)) hprev
  have hs := isModuleComplete_pi R f (fun n ↦ (K n).homology i) hsame
  apply isModuleComplete_extension R f (complexTowerMilnorSequence R K t i)
    (complexTowerMilnorSequence_shortExact R K t i)
  · exact isModuleComplete_coker R f (M := ModuleCat.of R (∀ n, (K n).homology (i - 1)))
      (N := ModuleCat.of R (∀ n, (K n).homology (i - 1)))
      (complexTowerHomologyDifference R K t (i - 1)) hp hp
  · exact isModuleComplete_ker R f (M := ModuleCat.of R (∀ n, (K n).homology i))
      (N := ModuleCat.of R (∀ n, (K n).homology i)) (complexTowerHomologyDifference R K t i) hs hs

/-- Koszul完備化候補の全次数のホモロジー加群は、各座標に関して導来完備。 -/
theorem koszulCompletionComplex_homology_isModuleComplete {e : ℕ}
    (a : Fin e → R) (j : Fin e) (i : ℤ) :
    IsModuleComplete R (a j) ((koszulCompletionComplex R a).homology i) :=
  complexTowerHomology_isModuleComplete_of_stages R (a j)
    (powerKoszulTower R a) (powerKoszulTransition R a) i
    (fun n ↦ powerKoszulStage_homology_isModuleComplete R a n j (i - 1))
    (fun n ↦ powerKoszulStage_homology_isModuleComplete R a n j i)

/-- 特にH⁰は、各座標に関して導来完備な加群。環構造は別工程。 -/
theorem koszulCompletionH0_isModuleComplete {e : ℕ} (a : Fin e → R) (j : Fin e) :
    IsModuleComplete R (a j) ((koszulCompletionComplex R a).homology 0) :=
  koszulCompletionComplex_homology_isModuleComplete R a j 0

end SerrePositivity.DerivedCompletion

end TowerHomologyCompletePart

section ComplexCompletionHomologyCompletePart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)

/-- Every homology module of a power-Koszul stage is complete, without bounds on its source. -/
lemma complexPowerKoszulStage_homology_isModuleComplete
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) (i : ℤ) :
    IsModuleComplete R a ((complexPowerKoszulStage R a K n).homology i) := by
  apply isModuleComplete_of_pow_smul_zero R a _ n
  have h := (scalarConeCoordinateNullHomotopy (a ^ n) K).homologyMap_eq i
  rw [smulId, homologyMap_smul, homologyMap_id, homologyMap_zero] at h
  intro x
  exact congrArg (fun f ↦ f.hom x) h

/-- All homology of the concrete completion is complete, retaining both Milnor contributions. -/
lemma complexCompletionFunctor_homology_isModuleComplete
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    IsModuleComplete R a (((complexCompletionFunctor R a).obj K).homology i) :=
  complexTowerHomology_isModuleComplete_of_stages R a
    (complexPowerKoszulStage R a K) (complexPowerKoszulTransition R a K) i
    (fun n ↦ complexPowerKoszulStage_homology_isModuleComplete R a K n (i - 1))
    (fun n ↦ complexPowerKoszulStage_homology_isModuleComplete R a K n i)

/-- The actual completion functor has complete actual homology modules in every degree. -/
lemma derivedComplexCompletionFunctor_homology_isModuleComplete
    (X : ConcreteDerivedCategory R) (i : ℤ) :
    IsModuleComplete R a ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      ((derivedComplexCompletionFunctor R a).obj X)) := by
  let K := DerivedCategory.Q.objPreimage X
  let e : complexCompletionObject R a K ≅ (derivedComplexCompletionFunctor R a).obj X :=
    (derivedComplexCompletionComparison R a).symm.app K ≪≫
      (derivedComplexCompletionFunctor R a).mapIso (DerivedCategory.Q.objObjPreimageIso X)
  let h := (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).symm.app
      ((complexCompletionFunctor R a).obj K) ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso e
  exact isModuleComplete_of_linearEquiv R a _ _ h.toLinearEquiv
    (complexCompletionFunctor_homology_isModuleComplete R a K i)

/-- Derived completeness implies module completeness of every actual homology module. -/
lemma isComplete_homology_isModuleComplete
    (X : ConcreteDerivedCategory R) (hX : IsComplete R a X) (i : ℤ) :
    IsModuleComplete R a ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj X) := by
  let e := (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
    (derivedComplexCompletionUnitIso R a X hX).symm
  exact isModuleComplete_of_linearEquiv R a _ _ e.toLinearEquiv
    (derivedComplexCompletionFunctor_homology_isModuleComplete R a X i)

end SerrePositivity.DerivedCompletion

end ComplexCompletionHomologyCompletePart

section TermwiseCompletePart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)

/-- The scalar-tower difference is an actual isomorphism when every term is
derived complete. -/
lemma scalarComplexTowerDifference_isIso_of_terms
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ i, IsModuleComplete R a (K.X i)) :
    IsIso (complexTowerDifference R (constantComplexTower R K) (fun _ => smulId a K)) := by
  let d := complexTowerDifference R (constantComplexTower R K) (fun _ => smulId a K)
  have he (i : ℤ) (x : (piObj (constantComplexTower R K)).X i) :
      complexProductDegreeEquiv R (constantComplexTower R K) i (d.f i x) =
        adicRecurrenceMap (M := K.X i) a
          (complexProductDegreeEquiv R (constantComplexTower R K) i x) := by
    funext n
    exact complexProductDegreeEquiv_difference R _ _ i x n
  have hIso (i : ℤ) : IsIso (d.f i) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    let e := complexProductDegreeEquiv R (constantComplexTower R K) i
    have hb := (isModuleComplete_iff_recurrence_bijective R a (K.X i)).mp (hK i)
    constructor
    · intro x y hxy
      apply e.injective
      apply hb.injective
      rw [← he i x, ← he i y, hxy]
    · intro y
      obtain ⟨z, hz⟩ := hb.surjective (e y)
      refine ⟨e.symm z, e.injective ?_⟩
      rw [he]
      exact (congrArg (adicRecurrenceMap (M := K.X i) a) (e.apply_symm_apply z)).trans hz
  exact HomologicalComplex.Hom.isIso_of_components d

/-- Termwise derived completeness implies completeness of the actual derived
image of an arbitrary cochain complex. -/
lemma isComplete_Q_of_terms
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ i, IsModuleComplete R a (K.X i)) :
    IsComplete R a (DerivedCategory.Q.obj K) := by
  apply (isComplete_iff_scalarComplexTowerHomotopyLimit_acyclic R a K).mpr
  have := scalarComplexTowerDifference_isIso_of_terms R a K hK
  exact cochainAcyclic_shift
    ((cochain_quasiIso_iff_cone_acyclic _).mp inferInstance) (-1)

end SerrePositivity.DerivedCompletion

end TermwiseCompletePart

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.2.3.25" (partial := direction) "仮定：通常可換環 R、一元 a と a 導来完備な通常の導来対象（Lean が強い：主元の通常導来模型）。結論：全次数の実ホモロジー加群が a 完備となる（原典 (1) の S-complete と印字された向きの主元版に一致）。逆向き、S-local と印字された後続の t 構造、局所化の t 完全性は含まれない。"] _root_.SerrePositivity.DerivedCompletion.isComplete_homology_isModuleComplete
