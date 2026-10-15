module
public import SerrePositivity.HomologicalAlgebra.IdealPowerTorsionSupport
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Independence of the coefficient ring for ideal-power torsion -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
variable {R D : Type u} [CommRing R] [CommRing D]

/-- An ideal annihilates an element after restriction precisely when its image does before it. -/
lemma torsionBySet_restrictScalars_iff_map (φ : R →+* D) (I : Ideal R)
    (M : ModuleCat.{u} D) (x : M) :
    x ∈ Submodule.torsionBySet R ((ModuleCat.restrictScalars φ).obj M) (I : Set R) ↔
      x ∈ Submodule.torsionBySet D M (I.map φ : Set D) := by
  constructor
  · intro h
    have h' : ∀ a : I, φ a • x = 0 :=
      (Submodule.mem_torsionBySet_iff (R := R)
        (M := (ModuleCat.restrictScalars φ).obj M) (I : Set R)
        (x : (ModuleCat.restrictScalars φ).obj M)).mp h
    have hI : I ≤ (Ideal.torsionOf D M x).comap φ := by
      intro a ha
      change φ a • x = 0
      exact h' ⟨a, ha⟩
    have hmap : I.map φ ≤ Ideal.torsionOf D M x := Ideal.map_le_iff_le_comap.mpr hI
    apply (Submodule.mem_torsionBySet_iff (R := D) (M := M) (I.map φ : Set D) x).mpr
    intro a
    exact hmap a.property
  · intro h
    have h' := (Submodule.mem_torsionBySet_iff (R := D) (M := M) (I.map φ : Set D) x).mp h
    apply (Submodule.mem_torsionBySet_iff (R := R)
        (M := (ModuleCat.restrictScalars φ).obj M) (I : Set R)
      (x : (ModuleCat.restrictScalars φ).obj M)).mpr
    intro a
    exact h' ⟨φ a, Ideal.mem_map_of_mem φ a.property⟩

/-- The same equivalence holds for elements killed by some ideal power. -/
lemma primaryComponent_restrictScalars_iff_map (φ : R →+* D) (I : Ideal R)
    (M : ModuleCat.{u} D) (x : M) :
    x ∈ I.primaryComponent ((ModuleCat.restrictScalars φ).obj M) ↔
      x ∈ (I.map φ).primaryComponent M := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem
      ((ModuleCat.restrictScalars φ).obj M) I (x : (ModuleCat.restrictScalars φ).obj M)).mp h
    apply (Ideal.primaryComponent_mem M (I.map φ) x).mpr
    refine ⟨n, ?_⟩
    simpa only [Ideal.map_pow] using (torsionBySet_restrictScalars_iff_map φ (I ^ n) M x).mp hn
  · intro h
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M (I.map φ) x).mp h
    apply (Ideal.primaryComponent_mem ((ModuleCat.restrictScalars φ).obj M) I
      (x : (ModuleCat.restrictScalars φ).obj M)).mpr
    refine ⟨n, ?_⟩
    apply (torsionBySet_restrictScalars_iff_map φ (I ^ n) M x).mpr
    simpa only [Ideal.map_pow] using hn

/-- Coefficient restriction identifies the actual torsion submodules by the identity on elements. -/
def idealPowerTorsionRestrictScalarsEquiv (φ : R →+* D) (I : Ideal R) (M : ModuleCat.{u} D) :
    I.primaryComponent ((ModuleCat.restrictScalars φ).obj M) ≃ₗ[R]
      (ModuleCat.restrictScalars φ).obj ((idealPowerTorsionFunctor (I.map φ)).obj M) where
  toFun x := ⟨x.val, (primaryComponent_restrictScalars_iff_map φ I M x.val).mp x.property⟩
  invFun x := ⟨x.val, (primaryComponent_restrictScalars_iff_map φ I M x.val).mpr x.property⟩
  left_inv _x := Subtype.ext rfl
  right_inv _x := Subtype.ext rfl
  map_add' _x _y := Subtype.ext rfl
  map_smul' _r _x := Subtype.ext rfl

/-- The actual torsion functor commutes with restriction of scalars, naturally in all D-modules. -/
def idealPowerTorsionRestrictScalarsNatIso (φ : R →+* D) (I : Ideal R) :
    ModuleCat.restrictScalars φ ⋙ idealPowerTorsionFunctor I ≅
      idealPowerTorsionFunctor (I.map φ) ⋙ ModuleCat.restrictScalars φ :=
  NatIso.ofComponents (fun M => (idealPowerTorsionRestrictScalarsEquiv φ I M).toModuleIso)
    (by intro M N f; ext x; rfl)

/-- A change of coefficient ring followed by a change of support radical, naturally on modules. -/
def idealPowerTorsionRestrictScalarsSupportNatIso [IsNoetherianRing D]
    (φ : R →+* D) (I : Ideal R) (J : Ideal D) (h : (I.map φ).radical = J.radical) :
    ModuleCat.restrictScalars φ ⋙ idealPowerTorsionFunctor I ≅
      idealPowerTorsionFunctor J ⋙ ModuleCat.restrictScalars φ :=
  idealPowerTorsionRestrictScalarsNatIso φ I ≪≫
    Functor.isoWhiskerRight (idealPowerTorsionRadicalNatIso (I.map φ) J
      (IsNoetherian.noetherian _) (IsNoetherian.noetherian _) h) (ModuleCat.restrictScalars φ)

end SerrePositivity
