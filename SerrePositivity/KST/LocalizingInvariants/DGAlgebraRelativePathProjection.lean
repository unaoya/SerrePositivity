module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativePathEndpoints
public import SerrePositivity.KST.LocalizingInvariants.CochainPullbackQuasiIso

/-!
概要：全射準同型の相対経路の実射影・対角・両評価も準同型となる。
方針：実経路射の全射性と準同型性を底変更し、厳密な切断式へ接続する。
規約：相対二端点射の準同型性は別工程。使われ方：相対持ち上げの導来比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativePath
variable (R : Type u) [CommRing R] {C B : Mon (Complex R)} (p : C ⟶ B)
  (hs : ∀ n : ℤ, Function.Surjective (p.hom.f n)) (hq : QuasiIso p.hom)

include hs in
lemma pathMap_epi : Epi (Path.map R p).hom :=
  HomologicalComplex.epi_of_epi_f _
    (fun n => (ModuleCat.epi_iff_surjective _).2 (Path.map_surjective R p hs n))

include hs in
lemma projection_surjective (n : ℤ) : Function.Surjective ((projection R p).hom.f n) := by
  have := pathMap_epi R p hs
  exact cochainPullback_snd_surjective (Path.map R p).hom (Path.diagonal R B).hom n

include hs hq in
lemma projection_quasiIso : QuasiIso (projection R p).hom := by
  have := pathMap_epi R p hs
  exact cochainPullback_snd_quasiIso (Path.map R p).hom (Path.diagonal R B).hom
    (Path.map_quasiIso R p hq)

include hs hq in
lemma diagonal_quasiIso : QuasiIso (diagonal R p).hom := by
  have := projection_quasiIso R p hs hq
  have : QuasiIso ((diagonal R p).hom ≫ (projection R p).hom) := by
    change QuasiIso ((diagonal R p ≫ projection R p).hom)
    rw [diagonal_projection]
    exact hq
  exact quasiIso_of_comp_right (diagonal R p).hom (projection R p).hom

include hs hq in
lemma source_quasiIso : QuasiIso (source R p).hom := by
  have := diagonal_quasiIso R p hs hq
  have : QuasiIso ((diagonal R p).hom ≫ (source R p).hom) := by
    change QuasiIso ((diagonal R p ≫ source R p).hom)
    rw [diagonal_source]
    infer_instance
  exact quasiIso_of_comp_left (diagonal R p).hom (source R p).hom

include hs hq in
lemma target_quasiIso : QuasiIso (target R p).hom := by
  have := diagonal_quasiIso R p hs hq
  have : QuasiIso ((diagonal R p).hom ≫ (target R p).hom) := by
    change QuasiIso ((diagonal R p ≫ target R p).hom)
    rw [diagonal_target]
    infer_instance
  exact quasiIso_of_comp_left (diagonal R p).hom (target R p).hom

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativePath
