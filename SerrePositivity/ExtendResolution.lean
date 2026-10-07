module

public import SerrePositivity.ResolutionOfCochain
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# ℕ 添字の射影分解を ℤ 添字 cochain 複体に延長する

`P : ProjectiveResolution X` に対して `extRes P := P.complex.extend embUp`（`n ↦ -n` に沿った延長）
は `IsResolutionOf (extRes P) X` をみたす。また射 `f : X ⟶ Y` の持ち上げ `lift f P Q` の延長
`extLift P f Q` は、`H^0(extRes P) ≅ X`、`H^0(extRes Q) ≅ Y` のもとで `f` に対応する。

Tor の長完全列（`Descent/TorLES.lean`）で、持ち上げの写像錐をとるために使う。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {R : Type u} [CommRing R]

lemma embUp_f_zero : embUp.f 0 = 0 := by
  change (0 : ℤ) - 0 = 0
  simp

variable {X : ModuleCat.{u} R} (P : ProjectiveResolution X)

/-- 射影分解の ℤ 添字 cochain 複体への延長。 -/
noncomputable abbrev extRes : CochainComplex (ModuleCat.{u} R) ℤ :=
  P.complex.extend embUp

lemma extRes_isZero_X (i : ℤ) (hi : 0 < i) : IsZero ((extRes P).X i) :=
  HomologicalComplex.isZero_extend_X _ _ _ (fun n hn ↦ by
    have : (0 : ℤ) - n = i := hn
    omega)

lemma extRes_projective (i : ℤ) : Projective ((extRes P).X i) := by
  by_cases h : ∃ n : ℕ, embUp.f n = i
  · obtain ⟨n, rfl⟩ := h
    exact Projective.of_iso (P.complex.extendXIso embUp rfl).symm (P.projective n)
  · exact (HomologicalComplex.isZero_extend_X _ _ _ (fun n hn ↦ h ⟨n, hn⟩)).projective

/-- `H_n(P) = 0 (n ≠ 0)`：`π` が擬同型なので。 -/
lemma res_homology_isZero (n : ℕ) (hn : n ≠ 0) : IsZero (P.complex.homology n) :=
  haveI : IsIso (HomologicalComplex.homologyMap P.π n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance
  (asIso (HomologicalComplex.homologyMap P.π n)).isZero_iff.mpr
    (HomologicalComplex.isZero_single_obj_homology _ _ _ _ hn)

lemma extRes_isZero_homology (i : ℤ) (hi : i ≠ 0) : IsZero ((extRes P).homology i) := by
  by_cases h : ∃ n : ℕ, embUp.f n = i
  · obtain ⟨n, rfl⟩ := h
    refine (P.complex.extendHomologyIso embUp rfl).isZero_iff.mpr (res_homology_isZero P n ?_)
    rintro rfl
    exact hi rfl
  · exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
      (HomologicalComplex.extend_exactAt _ _ _ (fun n hn ↦ h ⟨n, hn⟩))

/-- `H^0(extRes P) ≅ X`。 -/
noncomputable def extResHomologyZeroIso : (extRes P).homology 0 ≅ X :=
  haveI : IsIso (HomologicalComplex.homologyMap P.π 0) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance
  P.complex.extendHomologyIso embUp (j := 0) (j' := 0) embUp_f_zero ≪≫
    asIso (HomologicalComplex.homologyMap P.π 0) ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0 X

/-- `extRes P` は `X` の分解。 -/
noncomputable def isResolutionOf_extRes : IsResolutionOf (extRes P) X where
  isZero_X := extRes_isZero_X P
  projective := extRes_projective P
  isZero_homology := extRes_isZero_homology P
  homologyZeroIso := extResHomologyZeroIso P

/-- 持ち上げの延長。 -/
noncomputable abbrev extLift {Y : ModuleCat.{u} R} (f : X ⟶ Y) (Q : ProjectiveResolution Y) :
    extRes P ⟶ extRes Q :=
  HomologicalComplex.extendMap (ProjectiveResolution.lift f P Q) embUp

/-- 持ち上げの延長は `H^0` で `f` に対応する。 -/
lemma extLift_homologyZero {Y : ModuleCat.{u} R} (f : X ⟶ Y) (Q : ProjectiveResolution Y) :
    HomologicalComplex.homologyMap (extLift P f Q) 0 ≫ (extResHomologyZeroIso Q).hom =
      (extResHomologyZeroIso P).hom ≫ f := by
  have h1 := HomologicalComplex.extendHomologyIso_hom_naturality
    (ProjectiveResolution.lift f P Q) embUp (j := 0) (j' := 0) embUp_f_zero
  have h2 : HomologicalComplex.homologyMap (ProjectiveResolution.lift f P Q) 0 ≫
      HomologicalComplex.homologyMap Q.π 0 =
      HomologicalComplex.homologyMap P.π 0 ≫
        HomologicalComplex.homologyMap ((ChainComplex.single₀ (ModuleCat.{u} R)).map f) 0 := by
    rw [← HomologicalComplex.homologyMap_comp, ProjectiveResolution.lift_commutes,
      HomologicalComplex.homologyMap_comp]
  have h3 := HomologicalComplex.singleObjHomologySelfIso_hom_naturality (ComplexShape.down ℕ) 0 f
  simp only [extResHomologyZeroIso, Iso.trans_hom, asIso_hom]
  rw [← Category.assoc, h1, Category.assoc, ← Category.assoc
    (HomologicalComplex.homologyMap (ProjectiveResolution.lift f P Q) 0), h2, Category.assoc,
    Category.assoc, h3]
  simp only [Category.assoc]

end SerrePositivity
