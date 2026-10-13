module

public import SerrePositivity.LengthAlgebra.RootTowerLength.FiniteStage
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.TensorProduct.Lift

/-! # Finite generation and the raw normalized-length functions

This module proves comparisons from the definitions and finite-stage module lengths.
It does not use the additivity input or the assembled `NormalizedLength` structure.
-/

@[expose] public section

set_option linter.style.haveILetI false

universe u
open IsLocalRing TensorProduct
open scoped ENNReal

namespace SerrePositivity.Section2

variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ)

/-- A finite family in a base change to the root tower is represented at one later stage. -/
theorem exists_tower_tensor_family_stage (n : ℕ) (V : Type u) [AddCommGroup V]
    [Module (TowerStage A t p n) V] {ι : Type*} [Finite ι]
    (q : ι → Tower A t p ⊗[TowerStage A t p n] V) :
    ∃ (N : ℕ) (hnN : n ≤ N),
      letI := (towerMap A t p n N hnN).toRingHom.toAlgebra
      letI := isScalarTower_towerMap_tower A t p n N hnN
      ∃ w : ι → TowerStage A t p N ⊗[TowerStage A t p n] V,
        ∀ j, TensorProduct.AlgebraTensorModule.cancelBaseChange (TowerStage A t p n)
          (TowerStage A t p N) (Tower A t p) (Tower A t p) V (1 ⊗ₜ w j) = q j := by
  classical
  letI := Fintype.ofFinite ι
  choose k a v hv using fun j ↦ TensorProduct.exists_sum_tmul_eq (q j)
  obtain ⟨m, c, hc⟩ := exists_towerOf_family A t p
    (fun z : Σ j, Fin (k j) ↦ a z.1 z.2)
  let N := n ⊔ m
  have hnN : n ≤ N := le_sup_left
  have hmN : m ≤ N := le_sup_right
  letI := (towerMap A t p n N hnN).toRingHom.toAlgebra
  letI := isScalarTower_towerMap_tower A t p n N hnN
  let w (j : ι) : TowerStage A t p N ⊗[TowerStage A t p n] V :=
    ∑ l, towerMap A t p m N hmN (c ⟨j, l⟩) ⊗ₜ v j l
  refine ⟨N, hnN, w, fun j ↦ ?_⟩
  rw [hv j]
  simp only [w, TensorProduct.tmul_sum, map_sum,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def, mul_one]
  congr 1
  ext l
  congr 1
  change towerOf A t p N (towerMap A t p m N hmN (c ⟨j, l⟩)) = _
  rw [towerOf_towerMap, hc]

variable [IsLocalRing A] [IsNoetherianRing A] [Fact p.Prime]
  (ht : ∀ i, t i ∈ maximalIdeal A)

include ht

/-- A finitely generated submodule of a quotient of a finite-stage base change has
raw length at most the normalized length of that finite-stage module. -/
theorem fgLength_submodule_le_stage_cover (n : ℕ) (V : Type u) [AddCommGroup V]
    [Module (TowerStage A t p n) V] (hV : IsFiniteLength (TowerStage A t p n) V)
    {M : Type u} [AddCommGroup M] [Module (Tower A t p) M]
    (f : Tower A t p ⊗[TowerStage A t p n] V →ₗ[Tower A t p] M)
    (hf : Function.Surjective f) (N : Submodule (Tower A t p) M) (hN : N.FG) :
    fgLength A t p N ≤
      (Module.length (TowerStage A t p n) V : ℝ≥0∞) / (stageRank h p n : ℝ≥0∞) := by
  classical
  haveI : Module.Finite (Tower A t p) N := Module.Finite.iff_fg.mpr hN
  obtain ⟨r, z, hz⟩ := Module.Finite.exists_fin (R := Tower A t p) (M := N)
  choose q hq using fun j ↦ hf (z j : M)
  obtain ⟨k, hnk, w, hw⟩ := exists_tower_tensor_family_stage A t p n V q
  letI := (towerMap A t p n k hnk).toRingHom.toAlgebra
  letI := isScalarTower_towerMap_tower A t p n k hnk
  let Q := TowerStage A t p k ⊗[TowerStage A t p n] V
  let K : Submodule (TowerStage A t p k) Q :=
    Submodule.span (TowerStage A t p k) (Set.range w)
  letI : Module (TowerStage A t p k) M :=
    Module.compHom M (algebraMap (TowerStage A t p k) (Tower A t p))
  letI : IsScalarTower (TowerStage A t p k) (Tower A t p) M :=
    IsScalarTower.of_compHom _ _ _
  letI : Module (TowerStage A t p k) N :=
    Module.compHom N (algebraMap (TowerStage A t p k) (Tower A t p))
  letI : IsScalarTower (TowerStage A t p k) (Tower A t p) N :=
    IsScalarTower.of_compHom _ _ _
  let E := TensorProduct.AlgebraTensorModule.cancelBaseChange (TowerStage A t p n)
    (TowerStage A t p k) (Tower A t p) (Tower A t p) V
  let F : Q →ₗ[TowerStage A t p k] M :=
    ((f.comp E.toLinearMap).restrictScalars (TowerStage A t p k)).comp
      (TensorProduct.mk (TowerStage A t p k) (Tower A t p) Q 1)
  have hF : K ≤ (N.restrictScalars (TowerStage A t p k)).comap F := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    change f (E (1 ⊗ₜ w j)) ∈ N
    rw [hw j, hq j]
    exact (z j).property
  let FK : K →ₗ[TowerStage A t p k] N :=
    { toFun := fun x ↦ ⟨F x, hF x.property⟩
      map_add' := fun x y ↦ Subtype.ext (F.map_add x y)
      map_smul' := fun a x ↦ Subtype.ext (F.map_smul a x) }
  let L := FK.liftBaseChange (Tower A t p)
  have hL : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, ← top_le_iff, ← hz, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨1 ⊗ₜ (⟨w j, Submodule.subset_span (Set.mem_range_self j)⟩ : K), ?_⟩
    apply Subtype.ext
    change (1 : Tower A t p) • f (E (1 ⊗ₜ w j)) = (z j : M)
    rw [one_smul, hw j, hq j]
  have hQ : IsFiniteLength (TowerStage A t p k) Q := by
    rw [← Module.length_ne_top_iff]
    change Module.length (TowerStage A t p k)
      (TowerStage A t p k ⊗[TowerStage A t p n] V) ≠ ⊤
    rw [length_tensor_towerMap A t p n k hnk ht]
    obtain ⟨l, hl⟩ := ENat.ne_top_iff_exists.mp (Module.length_ne_top_iff.mpr hV)
    rw [← hl, ← Nat.cast_mul]
    exact ENat.natCast_ne_top _
  have hK : IsFiniteLength (TowerStage A t p k) K :=
    IsFiniteLength.of_injective hQ (Submodule.subtype_injective K)
  calc
    fgLength A t p N ≤ fgLength A t p (Tower A t p ⊗[TowerStage A t p k] K) :=
      fgLength_le_of_surjective L hL
    _ = (Module.length (TowerStage A t p k) K : ℝ≥0∞) /
        (stageRank h p k : ℝ≥0∞) := fgLength_tensor A t p ht k K hK
    _ ≤ (Module.length (TowerStage A t p k) Q : ℝ≥0∞) /
        (stageRank h p k : ℝ≥0∞) := ENNReal.div_le_div_right
      (ENat.toENNReal_le.mpr (Module.length_le_of_injective K.subtype
        (Submodule.subtype_injective K))) _
    _ = (Module.length (TowerStage A t p n) V : ℝ≥0∞) /
        (stageRank h p n : ℝ≥0∞) := by
      dsimp only [Q]
      rw [length_tensor_towerMap A t p n k hnk ht]
      simp only [ENat.toENNReal_mul, ENat.toENNReal_coe]
      have hd := div_stageRank_eq (h := h) p n k k hnk le_rfl
        (Module.length (TowerStage A t p n) V : ℝ≥0∞)
      simpa only [Nat.sub_self, stageRank, zero_mul, pow_zero, Nat.cast_one, one_mul]
        using hd.symm

/-- The raw finite-generation length is monotone on finitely generated submodules.
This uses finite-stage submodule lengths, without any additivity or C1 input. -/
theorem fgLength_submodule_le {M : Type u} [AddCommGroup M]
    [Module (Tower A t p) M] (N : Submodule (Tower A t p) M) (hN : N.FG) :
    fgLength A t p N ≤ fgLength A t p M := by
  unfold fgLength
  refine le_iInf fun P ↦ le_iInf fun i₁ ↦ le_iInf fun i₂ ↦ le_iInf fun hP ↦
    le_iInf fun f ↦ le_iInf fun hf ↦ ?_
  unfold presentedLength
  refine le_iInf fun n ↦ le_iInf fun V ↦ le_iInf fun j₁ ↦ le_iInf fun j₂ ↦
    le_iInf fun hV ↦ le_iInf fun ⟨e⟩ ↦ ?_
  exact fgLength_submodule_le_stage_cover A t p ht n V hV
    (f.comp e.symm.toLinearMap) (hf.comp e.symm.surjective) N hN

/-- On a finitely generated module the raw supremum equals its raw finite-generation
length. Noetherian locality, primality and coordinates in the maximal ideal suffice;
the stronger standard-power-series presentation of CLMST is not needed here. -/
theorem towerLengthFun_eq_fgLength_of_noetherian (M : Type u) [AddCommGroup M]
    [Module (Tower A t p) M] [Module.Finite (Tower A t p) M] :
    towerLengthFun A t p M = fgLength A t p M := by
  refine le_antisymm ?_ ?_
  · exact iSup₂_le fun N hN ↦ fgLength_submodule_le A t p ht N hN
  · have htop : (⊤ : Submodule (Tower A t p) M).FG := Module.Finite.fg_top
    have he := fgLength_congr (A := A) (t := t) (p := p)
      (Submodule.topEquiv : (⊤ : Submodule (Tower A t p) M) ≃ₗ[Tower A t p] M)
    exact he ▸ le_iSup₂_of_le (⊤ : Submodule (Tower A t p) M) htop le_rfl

/-- For a finitely presented power-torsion module, the raw presentation and
finite-generation definitions agree, using its finite-stage descent. -/
theorem presentedLength_eq_fgLength_of_noetherian (M : Type u) [AddCommGroup M]
    [Module (Tower A t p) M] [Module.FinitePresentation (Tower A t p) M]
    (hM : IsPowTorsion (towerMaxIdeal A t p) M) :
    presentedLength A t p M = fgLength A t p M := by
  obtain ⟨n, V, i₁, i₂, hV, _, ⟨e⟩⟩ := exists_descent A t p M hM
  refine le_antisymm ?_ (fgLength_le_presentedLength M)
  calc
    presentedLength A t p M ≤
        (Module.length (TowerStage A t p n) V : ℝ≥0∞) /
          (stageRank h p n : ℝ≥0∞) :=
      iInf_le_of_le n (iInf_le_of_le V (iInf_le_of_le i₁ (iInf_le_of_le i₂
        (iInf_le_of_le hV (iInf_le_of_le ⟨e⟩ le_rfl)))))
    _ = fgLength A t p M := by
      rw [fgLength_congr e, fgLength_tensor A t p ht n V hV]

/-- The raw supremum also agrees with the presentation value on finitely presented
power-torsion modules. Together with finite-generation equality this gives the
two agreement assertions in CLMST Proposition 2.2.3 under weaker base hypotheses. -/
theorem towerLengthFun_eq_presentedLength_of_noetherian (M : Type u) [AddCommGroup M]
    [Module (Tower A t p) M] [Module.FinitePresentation (Tower A t p) M]
    (hM : IsPowTorsion (towerMaxIdeal A t p) M) :
    towerLengthFun A t p M = presentedLength A t p M := by
  rw [towerLengthFun_eq_fgLength_of_noetherian A t p ht M,
    presentedLength_eq_fgLength_of_noetherian A t p ht M hM]

end SerrePositivity.Section2
