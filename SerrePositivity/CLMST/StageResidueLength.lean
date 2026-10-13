module

public import SerrePositivity.CLMST.StageLocality
public import SerrePositivity.CommutativeAlgebra.FiniteLocalSupport
public import SerrePositivity.CommutativeAlgebra.FiniteLength
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # 基底変更した有限段の共通剰余体と長さ

`D_n=A_n⊗_A D` の剰余体への全射を、D 上の根の段との同型から供給する。
A と D の共通剰余体の条件を A_n と D_n へ移し、係数制限が長さを保つことを示す。
D の局所性だけを使い、A の局所性、Noether 性、D の有限性や加群の有限長は要求しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.CLMST
open Section2 IsLocalRing CategoryTheory

variable (A D : Type u) [CommRing A] [CommRing D] [Algebra A D] [IsLocalRing D]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]

/-- D から基底変更した任意の有限段 D_n の剰余体への合成は全射。
D 上の根の段へ移し、その具体的な剰余体の記述を使う。 -/
theorem residue_surjective_stageAlgebra_D
    (htD : ∀ i, algebraMap A D (t i) ∈ maximalIdeal D) (n : ℕ) :
    let _ := stageAlgebra_isLocalRing A D t p htD n
    Function.Surjective ((residue (StageAlgebra A D t p n)).comp
      (algebraMap D (StageAlgebra A D t p n))) := by
  let := stageAlgebra_isLocalRing A D t p htD n
  let := isLocalRing_towerStage D (algebraMap A D ∘ t) p htD n
  let e := stageBaseChangeEquiv A D t p n
  let : IsLocalHom e.toRingEquiv.toRingHom := IsLocalHom.of_surjective _ e.surjective
  let er := ResidueField.mapEquiv e.toRingEquiv
  have hs := residue_surjective_towerStage D (algebraMap A D ∘ t) p htD n
  dsimp only
  intro x
  obtain ⟨d, hd⟩ := hs (er x)
  refine ⟨d, ?_⟩
  apply er.injective
  change ResidueField.map e.toRingEquiv.toRingHom
      (residue (StageAlgebra A D t p n) (algebraMap D (StageAlgebra A D t p n) d)) = er x
  rw [ResidueField.map_residue]
  change residue (TowerStage D (algebraMap A D ∘ t) p n)
    (e (algebraMap D (StageAlgebra A D t p n) d)) = er x
  rw [e.commutes]
  exact hd

/-- A と D が共通剰余体をもつなら、A から D_n の剰余体への合成も全射。 -/
theorem residue_surjective_stageAlgebra_base
    (htD : ∀ i, algebraMap A D (t i) ∈ maximalIdeal D)
    (hres : Function.Surjective ((residue D).comp (algebraMap A D))) (n : ℕ) :
    let _ := stageAlgebra_isLocalRing A D t p htD n
    Function.Surjective ((residue (StageAlgebra A D t p n)).comp
      (algebraMap A (StageAlgebra A D t p n))) := by
  let := stageAlgebra_isLocalRing A D t p htD n
  have hs := residue_surjective_stageAlgebra_D A D t p htD n
  let := isLocalHom_of_residue_surjective
    (algebraMap D (StageAlgebra A D t p n)) hs
  dsimp only
  intro x
  obtain ⟨d, hd⟩ := hs x
  obtain ⟨a, ha⟩ := hres (residue D d)
  refine ⟨a, ?_⟩
  change residue (StageAlgebra A D t p n) (algebraMap A (StageAlgebra A D t p n) a) = x
  rw [IsScalarTower.algebraMap_apply A D (StageAlgebra A D t p n),
    ← ResidueField.map_residue]
  change residue D (algebraMap A D a) = residue D d at ha
  rw [ha, ResidueField.map_residue]
  exact hd

/-- A_n と D_n の共通剰余体条件。D_n の剰余類を A の元で表し、A_n の定数として選ぶ。 -/
theorem residue_surjective_stageAlgebra_stage
    (htD : ∀ i, algebraMap A D (t i) ∈ maximalIdeal D)
    (hres : Function.Surjective ((residue D).comp (algebraMap A D))) (n : ℕ) :
    let _ := stageAlgebra_isLocalRing A D t p htD n
    Function.Surjective ((residue (StageAlgebra A D t p n)).comp
      (algebraMap (TowerStage A t p n) (StageAlgebra A D t p n))) := by
  let := stageAlgebra_isLocalRing A D t p htD n
  dsimp only
  intro x
  obtain ⟨a, ha⟩ := residue_surjective_stageAlgebra_base A D t p htD hres n x
  refine ⟨algebraMap A (TowerStage A t p n) a, ?_⟩
  change residue (StageAlgebra A D t p n)
    (algebraMap (TowerStage A t p n) (StageAlgebra A D t p n)
      (algebraMap A (TowerStage A t p n) a)) = x
  rw [← IsScalarTower.algebraMap_apply A (TowerStage A t p n) (StageAlgebra A D t p n)]
  exact ha

/-- D_n 加群の長さは A_n へ係数制限しても一致する。無限長の場合も含む。 -/
theorem length_stageAlgebra_eq
    (htD : ∀ i, algebraMap A D (t i) ∈ maximalIdeal D)
    (hres : Function.Surjective ((residue D).comp (algebraMap A D))) (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (StageAlgebra A D t p n) M]
    [Module (TowerStage A t p n) M]
    [IsScalarTower (TowerStage A t p n) (StageAlgebra A D t p n) M] :
    Module.length (TowerStage A t p n) M = Module.length (StageAlgebra A D t p n) M := by
  let := stageAlgebra_isLocalRing A D t p htD n
  exact length_eq_of_common_residueField
    (residue_surjective_stageAlgebra_stage A D t p htD hres n) M

/-- ModuleCat の係数制限で表した D_n 加群の長さも、A_n 上と D_n 上で一致する。 -/
theorem length_restrictScalars_stageAlgebra_eq
    (htD : ∀ i, algebraMap A D (t i) ∈ maximalIdeal D)
    (hres : Function.Surjective ((residue D).comp (algebraMap A D))) (n : ℕ)
    (M : ModuleCat.{u} (StageAlgebra A D t p n)) :
    Module.length (TowerStage A t p n)
      ((ModuleCat.restrictScalars (algebraMap (TowerStage A t p n)
        (StageAlgebra A D t p n))).obj M) = Module.length (StageAlgebra A D t p n) M := by
  let := stageAlgebra_isLocalRing A D t p htD n
  exact length_restrictScalars_eq
    (residue_surjective_stageAlgebra_stage A D t p htD hres n) M

end SerrePositivity.CLMST
