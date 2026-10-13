module

public import SerrePositivity.CommutativeAlgebra.ResidueFieldClosedExtension
public import SerrePositivity.CommutativeAlgebra.ResidueFieldStageMap

/-! # 最小元での初期段

空の開初期部分では基底環Bを使い、剰余体をBefore iへ同定して生成元iを加える。
旧段への条件は空添字から証明し、非空の場合と同じ閉延長の法則を満たす。
-/

public section
namespace SerrePositivity
open IsLocalRing
universe u
variable {B K : Type u} [CommRing B] [IsLocalRing B] [Field K]
variable [Algebra (ResidueField B) K] [Algebra B K] [IsScalarTower B (ResidueField B) K]
variable [LinearOrder K]

/-- 最小元の前の中間体を、基底の剰余体そのものへ同定する。 -/
noncomputable def residueFieldMinEquiv (i : K) (hi : IsMin i) :
    ResidueField B ≃ₐ[ResidueField B] residueGeneratorBefore (ResidueField B) K i :=
  (IntermediateField.botEquiv (ResidueField B) K).symm.trans
    (IntermediateField.equivOfEq (residueGeneratorBefore_eq_bot (ResidueField B) K i hi).symm)

/-- 最小元の初期段を、生成元を加えた閉初期部分の図式へ延長する。
Noether性は不要。旧段への写像・図式の条件は空添字から実際に供給する。 -/
theorem exists_closed_extension_of_min
    (i : K) (hi : IsMin i) (S : {j : K // j < i} → Type u)
    [∀ j, CommRing (S j)] [∀ j, IsLocalRing (S j)] [∀ j, Algebra B (S j)]
    (f : ∀ j k, j ≤ k → S j →ₐ[B] S k) (g : ∀ j, S j →ₐ[B] K) :
    ∃ (T : Type u) (_ : CommRing T) (_ : IsLocalRing T) (_ : Algebra B T)
      (_ : IsLocalHom (algebraMap B T)),
      ∃ (c : ∀ j, S j →ₐ[B] T) (gT : T →ₐ[B] K),
        IsResidueFieldClosedExtension i S f g T c gT := by
  let L := residueGeneratorBefore (ResidueField B) K i
  let E := IntermediateField.adjoin L {i}
  let eB := residueFieldMinEquiv (B := B) i hi
  have heB (y : ResidueField B) :
      eB.toRingEquiv (ResidueField.map (algebraMap B B) y) = algebraMap (ResidueField B) L y := by
    obtain ⟨b, rfl⟩ := residue_surjective (R := B) y
    rw [ResidueField.map_residue]
    exact eB.commutes (residue B b)
  obtain ⟨T, tRing, tLocal, tAlgOld, tAlgB, tTower, tHomOld, tHomB,
    tFlatOld, tFlatB, tNoeth, htOldMax, htBmax, eE, heE, heStep, t, ht⟩ :=
    exists_residueField_successor B B K L eB.toRingEquiv heB (by simp) i
  let : Module.Flat B T := tFlatB
  let v : E ≃ₐ[ResidueField B] residueGeneratorAfter (ResidueField B) K i :=
    IntermediateField.equivOfEq (residueGeneratorAfter_eq_adjoin (ResidueField B) K i).symm
  let eT : ResidueField T ≃+* residueGeneratorAfter (ResidueField B) K i :=
    eE.trans v.toRingEquiv
  have heT (y : ResidueField B) :
      eT (ResidueField.map (algebraMap B T) y) =
        algebraMap (ResidueField B) (residueGeneratorAfter (ResidueField B) K i) y := by
    change v (eE (ResidueField.map (algebraMap B T) y)) = _
    rw [heE]
    exact v.commutes y
  have ht' : (eT (residue T t) : K) = i := by
    change (v (eE (residue T t)) : K) = i
    rw [ht]
    with_unfolding_all rfl
  let G : T →ₐ[B] K := residueFieldStageMap
    (residueGeneratorAfter (ResidueField B) K i) eT heT
  let c : ∀ j, S j →ₐ[B] T := fun j ↦ False.elim (hi.not_lt j.property)
  let : ∀ j, Module.Flat B (S j) := fun j ↦ False.elim (hi.not_lt j.property)
  let : DirectedSystem S (f · · ·) := by
    constructor
    · intro j x
      exact False.elim (hi.not_lt j.property)
    · intro l k j hjk hkl x
      exact False.elim (hi.not_lt j.property)
  refine ⟨T, tRing, tLocal, tAlgB, tHomB, c, G, ?_⟩
  apply isResidueFieldClosedExtension_of_cocone i S f g
    (fun j ↦ False.elim (hi.not_lt j.property))
    (fun j k h x ↦ False.elim (hi.not_lt j.property))
    (fun j k h ↦ False.elim (hi.not_lt j.property))
    (fun j ↦ False.elim (hi.not_lt j.property)) T c G htBmax
    (residueFieldStageMap_range _ eT heT) (residueFieldStageMap_ker _ eT heT) ⟨t, ht'⟩
    (fun j k h x ↦ False.elim (hi.not_lt j.property))
    (fun j x ↦ False.elim (hi.not_lt j.property))
    (fun j ↦ False.elim (hi.not_lt j.property))

end SerrePositivity
