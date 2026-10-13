module

public import SerrePositivity.CommutativeAlgebra.ResidueFieldSuccessor

/-! # 各段から指定体への写像

剰余体同型と中間体の包含から、段の環から指定体Kへの実際の代数写像を構成する。
核・像を計算し、後続段の剰余体写像の両立から環写像の両立を導く。
-/

public section
namespace SerrePositivity
open IsLocalRing
variable {B S K : Type*} [CommRing B] [IsLocalRing B]
variable [CommRing S] [IsLocalRing S] [Algebra B S] [IsLocalHom (algebraMap B S)]
variable [Field K] [Algebra (ResidueField B) K] [Algebra B K]
variable [IsScalarTower B (ResidueField B) K]
variable (L : IntermediateField (ResidueField B) K) (e : ResidueField S ≃+* L)
variable (he : ∀ y, e (ResidueField.map (algebraMap B S) y) = algebraMap (ResidueField B) L y)

/-- 剰余体同型を経由して指定体へ送る、基底環上の代数写像。 -/
@[expose] noncomputable def residueFieldStageMap : S →ₐ[B] K where
  __ := L.val.toRingHom.comp (e.toRingHom.comp (residue S))
  commutes' b := by
    change algebraMap L K (e (residue S (algebraMap B S b))) = algebraMap B K b
    rw [← ResidueField.map_residue, he]
    rw [← IsScalarTower.algebraMap_apply (ResidueField B) L K]
    exact (IsScalarTower.algebraMap_apply B (ResidueField B) K b).symm

/-- 段写像の元ごとの計算。 -/
@[simp] theorem residueFieldStageMap_apply (s : S) :
    residueFieldStageMap L e he s = (e (residue S s) : K) := rfl

/-- 段写像の核は、その段の極大イデアル。 -/
theorem residueFieldStageMap_ker :
    RingHom.ker (residueFieldStageMap L e he).toRingHom = maximalIdeal S := by
  ext s
  change (L.val (e (residue S s)) = 0) ↔ s ∈ maximalIdeal S
  rw [← residue_eq_zero_iff]
  constructor
  · intro h
    have h' : L.val (e (residue S s)) = L.val (e 0) := by
      simpa only [map_zero] using h
    exact e.injective (L.val.injective h')
  · intro h
    rw [h, map_zero, map_zero]

/-- 段写像の像は、指定した中間体全体である。 -/
theorem residueFieldStageMap_range :
    Set.range (residueFieldStageMap L e he) = (L : Set K) := by
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    exact (e (residue S s)).property
  · intro hx
    obtain ⟨y, hy⟩ := e.surjective ⟨x, hx⟩
    obtain ⟨s, hs⟩ := residue_surjective (R := S) y
    refine ⟨s, ?_⟩
    change (e (residue S s) : K) = x
    rw [hs, hy]

section Compatibility
variable {T : Type*} [CommRing T] [IsLocalRing T] [Algebra B T]
variable [IsLocalHom (algebraMap B T)]
variable (M : IntermediateField (ResidueField B) K) (eT : ResidueField T ≃+* M)
variable (heT : ∀ y, eT (ResidueField.map (algebraMap B T) y) = algebraMap (ResidueField B) M y)

/-- 剰余体同型の両立から、段の環から指定体への写像の両立が従う。 -/
theorem residueFieldStageMap_comp
    (f : S →ₐ[B] T) [IsLocalHom f.toRingHom]
    (hres : ∀ y, (eT (ResidueField.map f.toRingHom y) : K) = (e y : K)) :
    (residueFieldStageMap M eT heT).comp f = residueFieldStageMap L e he := by
  ext s
  change (eT (residue T (f.toRingHom s)) : K) = (e (residue S s) : K)
  rw [← ResidueField.map_residue f.toRingHom]
  exact hres (residue S s)

/-- 中間体の塔に沿った剰余体写像の両立を、指定体への写像の両立へ接続する。
後続段の構成が返す剰余体の等式を、そのままこの定理へ適用できる。 -/
theorem residueFieldStageMap_comp_of_residue_tower
    [Algebra L M] [IsScalarTower L M K]
    (f : S →ₐ[B] T) [IsLocalHom f.toRingHom]
    (hres : ∀ y, eT (ResidueField.map f.toRingHom y) = algebraMap L M (e y)) :
    (residueFieldStageMap M eT heT).comp f = residueFieldStageMap L e he := by
  apply residueFieldStageMap_comp L e he M eT heT f
  intro y
  rw [hres]
  exact (IsScalarTower.algebraMap_apply L M K (e y)).symm

end Compatibility
end SerrePositivity
