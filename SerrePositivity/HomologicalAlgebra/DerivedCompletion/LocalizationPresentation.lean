module

public import SerrePositivity.CommutativeAlgebra.Adic.Telescope
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt

/-! # 局所化の長さ一の自由分解

主元を反転する局所化のtelescopeを加群の圏の短完全列として登録する。
最初の二項は自由加群なので射影的である。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- 主元を反転する局所化のtelescope短複体。 -/
def localizationPresentation (f : R) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (ModuleCat.ofHom (localizationTelescopeMap R f))
    (ModuleCat.ofHom (localizationTelescopeToAway R f)) (by
      apply ModuleCat.hom_ext
      exact localizationTelescope_comp_eq_zero R f)

/-- 自由telescopeは短完全列を与える。 -/
theorem localizationPresentation_shortExact (f : R) :
    (localizationPresentation R f).ShortExact where
  exact := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
    (localizationTelescope_range_eq_ker R f)
  mono_f := (ModuleCat.mono_iff_injective _).mpr
    (localizationTelescopeMap_injective R f)
  epi_g := (ModuleCat.epi_iff_surjective _).mpr
    (localizationTelescopeToAway_surjective R f)

instance localizationPresentation_projective_X₁ (f : R) :
    Projective (localizationPresentation R f).X₁ := by
  change Projective (ModuleCat.of R (ℕ →₀ R))
  infer_instance

instance localizationPresentation_projective_X₂ (f : R) :
    Projective (localizationPresentation R f).X₂ := by
  change Projective (ModuleCat.of R (ℕ →₀ R))
  infer_instance

/-- 局所化からのExtは、次数二以上で消滅する。 -/
theorem localization_ext_eq_zero (f : R) (M : ModuleCat.{u} R) (n : ℕ)
    (e : CategoryTheory.Abelian.Ext (ModuleCat.of R (Localization.Away f)) M (n + 2)) :
    e = 0 := by
  let S := localizationPresentation R f
  have hS := localizationPresentation_shortExact R f
  obtain ⟨x, hx⟩ := CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃ hS M e
    (CategoryTheory.Abelian.Ext.eq_zero_of_projective _) (n₀ := n + 1) (by omega)
  rw [← hx, CategoryTheory.Abelian.Ext.eq_zero_of_projective x]
  simp
  rfl

/-- Ext¹の消滅は、自由分解の差分写像に沿うExt⁰の全射性と同値。 -/
theorem localization_ext_one_subsingleton_iff (f : R) (M : ModuleCat.{u} R) :
    Subsingleton (CategoryTheory.Abelian.Ext (ModuleCat.of R (Localization.Away f)) M 1) ↔
      Function.Surjective
        ((CategoryTheory.Abelian.Ext.mk₀ (localizationPresentation R f).f).precomp M
          (add_zero 0)) :=
  CategoryTheory.Abelian.Ext.one_subsingleton_iff_of_projective M _
    (localizationPresentation_shortExact R f) inferInstance

end SerrePositivity.DerivedCompletion
