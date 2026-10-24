module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroPro
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNonpositiveNativeInverseRoof

/-!
概要：π₀ の pro 同型から、零切断の実両三角形付き非正次数逆 roof を構成する。
方針：積と単位を保つ厳密な零切断逆を、恒等分母の roof として保持する。
規約：左細分も恒等。使われ方：有限 Postnikov 帰納の零段。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)

lemma postnikovZeroMap_exists_nonpositiveInverseRoof
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0))) (i : ℕ) :
    ∃ m, ∃ hi : i ≤ m,
      Nonempty (NonpositiveInverseRoof R (f.map (postnikovFunctor R 0)) i m hi) := by
  obtain ⟨m, hi, r, hl, hr⟩ := postnikovZeroMap_isProIso R f h₀ i
  refine ⟨m, hi, ⟨{
    roof := SurjectiveRoof.ofHom R r
    roof_nonpositive := postnikovComplex_nonpositive R (B.obj m).obj 0
    source := (A.map (postnikovFunctor R 0)).obj m
    source_nonpositive := postnikovComplex_nonpositive R (A.obj m).obj 0
    sourceProjection := 𝟙 _
    sourceProjection_epi := by change Epi (𝟙 _); infer_instance
    sourceProjection_quasiIso := by change QuasiIso (𝟙 _); infer_instance
    sourceLift := (f.map (postnikovFunctor R 0)).app m
    source_denominator := by simp only [SurjectiveRoof.ofHom, Category.id_comp, Category.comp_id]
    source_numerator := by simpa only [SurjectiveRoof.ofHom, Category.id_comp] using hl
    rightPath := ?_ }⟩⟩
  change Path.Witness R (r ≫ (f.map (postnikovFunctor R 0)).app i)
    (𝟙 _ ≫ (B.map (postnikovFunctor R 0)).transition hi)
  rw [hr, Category.id_comp]
  exact Path.Witness.refl _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
