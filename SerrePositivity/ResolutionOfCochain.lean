module

public import SerrePositivity.ToChain
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

/-!
# ℤ 添字 cochain 複体からの射影分解

`K` が `0` 以下の次数に乗り、各項が射影的で、`H^i(K) = 0 (i ≠ 0)`、`H^0(K) ≅ Z` のとき
（`IsResolutionOf K Z`）、`toChain K` は `Z` の `ProjectiveResolution` になる。
Koszul 複体（`KoszulResolution.lean`）と、射影分解の持ち上げの写像錐（`Descent/TorLES.lean`）に使う。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- ℤ 添字 cochain 複体 `K` が `Z` の分解であること。 -/
structure IsResolutionOf (K : CochainComplex (ModuleCat.{u} R) ℤ) (Z : ModuleCat.{u} R) where
  /-- 正の次数で零。 -/
  isZero_X : ∀ i : ℤ, 0 < i → IsZero (K.X i)
  /-- 各項は射影的。 -/
  projective : ∀ i : ℤ, Projective (K.X i)
  /-- `i ≠ 0` でホモロジーは零。 -/
  isZero_homology : ∀ i : ℤ, i ≠ 0 → IsZero (K.homology i)
  /-- `H^0(K) ≅ Z`。 -/
  homologyZeroIso : K.homology 0 ≅ Z

namespace IsResolutionOf

variable {K : CochainComplex (ModuleCat.{u} R) ℤ} {Z : ModuleCat.{u} R} (h : IsResolutionOf K Z)

/-- `(toChain K).opcycles 0 ≅ Z`。 -/
noncomputable def opcyclesIso : (toChain K).opcycles 0 ≅ Z :=
  (asIso ((toChain K).homologyι 0)).symm ≪≫ toChainHomologyIsoZero K h.isZero_X ≪≫
    h.homologyZeroIso

/-- 増大射 `toChain K ⟶ Z`（0 次に集中）。 -/
noncomputable def π : toChain K ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj Z :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨(toChain K).pOpcycles 0 ≫ h.opcyclesIso.hom, by
      rw [← Category.assoc, HomologicalComplex.d_pOpcycles, zero_comp]⟩

lemma π_f_zero : h.π.f 0 = (toChain K).pOpcycles 0 ≫ h.opcyclesIso.hom := by
  simp [π]

/-- 増大射は擬同型。 -/
instance π_quasiIso : QuasiIso h.π where
  quasiIsoAt m := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    cases m with
    | zero =>
      have h1 : HomologicalComplex.opcyclesMap h.π 0 =
          h.opcyclesIso.hom ≫ ((ChainComplex.single₀ (ModuleCat.{u} R)).obj _).pOpcycles 0 := by
        rw [← cancel_epi ((toChain K).pOpcycles 0), HomologicalComplex.p_opcyclesMap, π_f_zero]
        exact Category.assoc _ _ _
      have : IsIso (HomologicalComplex.opcyclesMap h.π 0) := by
        rw [h1]
        exact IsIso.comp_isIso' inferInstance
          (HomologicalComplex.isIso_pOpcycles _ 1 0 (by simp [ChainComplex.prev])
            (HomologicalComplex.single_obj_d _ _ _ _ _))
      have h2 := HomologicalComplex.homologyι_naturality h.π 0
      have : IsIso (HomologicalComplex.homologyMap h.π 0 ≫
          ((ChainComplex.single₀ (ModuleCat.{u} R)).obj _).homologyι 0) := by
        rw [h2]; infer_instance
      exact IsIso.of_isIso_comp_right _
        (((ChainComplex.single₀ (ModuleCat.{u} R)).obj _).homologyι 0)
    | succ m =>
      refine IsZero.isIso ?_ ?_ _
      · exact (toChainHomologyIsoSucc _ m).isZero_iff.mpr (h.isZero_homology _ (by omega))
      · exact HomologicalComplex.isZero_single_obj_homology _ _ _ _ (by omega)

/-- `toChain K` は `Z` の射影分解。 -/
noncomputable def toProjectiveResolution : ProjectiveResolution Z where
  complex := toChain K
  projective m := Projective.of_iso (K.restrictionXIso embUp rfl).symm (h.projective _)
  π := h.π

end IsResolutionOf

end SerrePositivity
