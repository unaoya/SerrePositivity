module

public import SerrePositivity.ConeLES
public import SerrePositivity.ExtendResolution
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# 持ち上げの写像錐は余核の分解

`A` 加群の短完全列 `0 → V₁ →f V₂ →g V₃ → 0` に対して、`V₁`、`V₂` の射影分解（ℤ 添字に延長したもの）
の間の `f` の持ち上げ `f̃` の写像錐 `Cone f̃` は `V₃` の分解（`IsResolutionOf`）になる：

- 正の次数で零、各項は射影的（直和）。
- `H^i(Cone f̃) = 0 (i ≠ 0)`：錐の長完全列（`Cone.exact₁₂₃`）から。`i = -1` では
  `H^0(f̃)`（`f` に対応）が単射であることを使う。
- `H^0(Cone f̃) ≅ coker(H^0 f̃) ≅ coker f ≅ V₃`。

Tor の長完全列（`Descent/TorLES.lean`）の `V₃` の分解として使う。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable (A : Type u) [CommRing A]

/-- `V` の（延長した）射影分解。 -/
noncomputable abbrev resV (V : Type u) [AddCommGroup V] [Module A V] :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  extRes (projectiveResolution (ModuleCat.of A V))

/-- `H^0(resV V) ≅ V`。 -/
noncomputable abbrev resVHomologyZeroIso (V : Type u) [AddCommGroup V] [Module A V] :
    (resV A V).homology 0 ≅ ModuleCat.of A V :=
  extResHomologyZeroIso (projectiveResolution (ModuleCat.of A V))

variable {A}
variable {V₁ V₂ V₃ : Type u} [AddCommGroup V₁] [Module A V₁] [AddCommGroup V₂] [Module A V₂]
  [AddCommGroup V₃] [Module A V₃]

/-- `f` の持ち上げの延長 `f̃ : resV V₁ ⟶ resV V₂`。 -/
noncomputable abbrev liftSES (f : V₁ →ₗ[A] V₂) : resV A V₁ ⟶ resV A V₂ :=
  extLift (projectiveResolution (ModuleCat.of A V₁)) (ModuleCat.ofHom f)
    (projectiveResolution (ModuleCat.of A V₂))

/-- `H^0(f̃)` は `f` に対応する。 -/
lemma homologyMap_liftSES_zero (f : V₁ →ₗ[A] V₂) :
    HomologicalComplex.homologyMap (liftSES f) 0 =
      (resVHomologyZeroIso A V₁).hom ≫ ModuleCat.ofHom f ≫ (resVHomologyZeroIso A V₂).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  exact extLift_homologyZero _ _ _

variable (f : V₁ →ₗ[A] V₂) (g : V₂ →ₗ[A] V₃)

/-- `H^0(f̃)` は単射（`f` が単射なので）。 -/
lemma mono_homologyMap_liftSES_zero (hf : Function.Injective f) :
    Mono (HomologicalComplex.homologyMap (liftSES f) 0) := by
  rw [homologyMap_liftSES_zero]
  have : Mono (ModuleCat.ofHom f) := (ModuleCat.mono_iff_injective _).mpr hf
  infer_instance

/-- `H^0(Cone f̃) ≃ V₃`。 -/
noncomputable def coneHomologyZeroEquiv (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    (Cone.cone (liftSES f)).homology 0 ≃ₗ[A] V₃ := by
  have h2 := Cone.exact₂ (liftSES f) 0
  have h3 := Cone.exact₃ (liftSES f) 0 1 rfl
  have hepi : Epi (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr (liftSES f)) 0) :=
    h3.epi_f ((extRes_isZero_homology _ 1 one_ne_zero).eq_zero_of_tgt _)
  have hsurj : Function.Surjective
      (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr (liftSES f)) 0).hom :=
    (ModuleCat.epi_iff_surjective _).mp hepi
  have hrk : LinearMap.range (HomologicalComplex.homologyMap (liftSES f) 0).hom =
      LinearMap.ker (HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr (liftSES f)) 0).hom :=
    (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp h2
  let e₁ := (resVHomologyZeroIso A V₁).toLinearEquiv
  let e₂ := (resVHomologyZeroIso A V₂).toLinearEquiv
  -- `range (H^0 f̃)` を `e₂` で移すと `range f`
  have hmap : (LinearMap.range (HomologicalComplex.homologyMap (liftSES f) 0).hom).map
      (e₂ : (resV A V₂).homology 0 →ₗ[A] V₂) = LinearMap.range f := by
    rw [← LinearMap.range_comp, homologyMap_liftSES_zero]
    have : (e₂ : (resV A V₂).homology 0 →ₗ[A] V₂) ∘ₗ
        ((resVHomologyZeroIso A V₁).hom ≫ ModuleCat.ofHom f ≫
          (resVHomologyZeroIso A V₂).inv).hom =
        f ∘ₗ (e₁ : (resV A V₁).homology 0 →ₗ[A] V₁) := by
      ext y
      simp [e₁, e₂]
    rw [this, LinearMap.range_comp_of_range_eq_top _ e₁.range]
  exact (LinearMap.quotKerEquivOfSurjective _ hsurj).symm.trans
    ((Submodule.quotEquivOfEq _ _ hrk.symm).trans
      ((Submodule.Quotient.equiv _ _ e₂ hmap).trans
        ((Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.mp hfg).symm).trans
          (LinearMap.quotKerEquivOfSurjective g hg))))

/-- **持ち上げの錐は余核の分解**。 -/
noncomputable def isResolutionOf_cone (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    IsResolutionOf (Cone.cone (liftSES f)) (ModuleCat.of A V₃) where
  isZero_X i hi := by
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨extRes_isZero_X _ _ (by omega), extRes_isZero_X _ _ hi⟩
  projective i := by
    have := extRes_projective (projectiveResolution (ModuleCat.of A V₁)) (i + 1)
    have := extRes_projective (projectiveResolution (ModuleCat.of A V₂)) i
    exact Projective.of_iso
      (HomologicalComplex.homotopyCofiber.XIsoBiprod (liftSES f) i (i + 1) rfl).symm
      inferInstance
  isZero_homology i hi := by
    by_cases hi1 : i = -1
    · subst hi1
      have h10 : (-1 : ℤ) + 1 = 0 := by norm_num
      have h3 := Cone.exact₃ (liftSES f) (-1) 0 h10
      have hz : IsZero ((resV A V₂).homology (-1)) := extRes_isZero_homology _ (-1) (by norm_num)
      have hmonoδ : Mono (Cone.δ (liftSES f) (-1) 0 h10) := h3.mono_g (hz.eq_zero_of_src _)
      have hcomp : Cone.δ (liftSES f) (-1) 0 h10 ≫
          HomologicalComplex.homologyMap (liftSES f) 0 = 0 :=
        comp_eq_zero_transport (Cone.S₁ (liftSES f) (-1) 0 h10) _ _ _ _ _
          (Cone.δ_square (liftSES f) (-1) 0 h10) (ConeSmul.e_naturality 0 (liftSES f))
      have := mono_homologyMap_liftSES_zero f hf
      have hδ : Cone.δ (liftSES f) (-1) 0 h10 = 0 := zero_of_comp_mono _ hcomp
      rw [IsZero.iff_id_eq_zero, ← cancel_mono (Cone.δ (liftSES f) (-1) 0 h10), Category.id_comp,
        zero_comp, hδ]
    · exact (Cone.exact₃ (liftSES f) i (i + 1) rfl).isZero_of_both_isZero
        (extRes_isZero_homology _ i hi) (extRes_isZero_homology _ (i + 1) (by omega))
  homologyZeroIso := (coneHomologyZeroEquiv f g hg hfg).toModuleIso

end SerrePositivity
