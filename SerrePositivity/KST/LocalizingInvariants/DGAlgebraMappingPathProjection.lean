module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMappingPath
public import SerrePositivity.KST.LocalizingInvariants.CochainPullbackQuasiIso

/-!
概要：mapping-path の実射影は全射準同型であり、元の始域からの切断も準同型。
方針：経路の source 評価の全射準同型性を底変更し、厳密な切断式を使う。
規約：元の代数射には準同型性を要求しない。使われ方：実因子分解と導来比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.MappingPath
variable (R : Type u) [CommRing R] {A B : Mon (Complex R)} (f : A ⟶ B)

lemma source_epi : Epi (Path.source R B).hom :=
  HomologicalComplex.epi_of_epi_f _
    (fun n => (ModuleCat.epi_iff_surjective _).2 (Path.source_surjective R B n))

lemma projection_surjective (n : ℤ) : Function.Surjective ((projection R f).hom.f n) := by
  have := source_epi (B := B) R
  exact cochainPullback_snd_surjective (Path.source R B).hom f.hom n

lemma projection_quasiIso : QuasiIso (projection R f).hom := by
  have := source_epi (B := B) R
  exact cochainPullback_snd_quasiIso (Path.source R B).hom f.hom (Path.source_quasiIso R B)

lemma section_quasiIso : QuasiIso (section_ R f).hom := by
  have := projection_quasiIso R f
  have : QuasiIso ((section_ R f).hom ≫ (projection R f).hom) := by
    change QuasiIso ((section_ R f ≫ projection R f).hom)
    rw [section_projection]
    infer_instance
  exact quasiIso_of_comp_right (section_ R f).hom (projection R f).hom

lemma target_quasiIso (hf : QuasiIso f.hom) : QuasiIso (target R f).hom := by
  have := section_quasiIso R f
  have : QuasiIso ((section_ R f).hom ≫ (target R f).hom) := by
    change QuasiIso ((section_ R f ≫ target R f).hom)
    rw [section_target]
    exact hf
  exact quasiIso_of_comp_left (section_ R f).hom (target R f).hom

lemma quasiIso_iff_target : QuasiIso f.hom ↔ QuasiIso (target R f).hom := by
  constructor
  · exact target_quasiIso R f
  · intro ht
    have h := quasiIso_comp (section_ R f).hom (target R f).hom
      (hφ := section_quasiIso R f) (hφ' := ht)
    change QuasiIso ((section_ R f ≫ target R f).hom) at h
    rw [section_target] at h
    exact h

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.MappingPath
