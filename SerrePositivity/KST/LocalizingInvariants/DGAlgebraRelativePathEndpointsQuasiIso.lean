module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativePathProjection

/-!
概要：全射準同型の上の相対二端点射は、元の両端を保った準同型となる。
方針：二端点の底変更射影と相対 source の準同型性を、厳密な因子分解へ渡す。
規約：相対二端点射の次数全射性は別工程。使われ方：持ち上げの相対経路比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativePath
variable (R : Type u) [CommRing R] {C B : Mon (Complex R)} (p : C ⟶ B)
  (hs : ∀ n : ℤ, Function.Surjective (p.hom.f n)) (hq : QuasiIso p.hom)

include hs hq in
lemma endpointsSource_quasiIso : QuasiIso (endpointsSource R p).hom := by
  have : Epi p.hom := HomologicalComplex.epi_of_epi_f _
    (fun n => (ModuleCat.epi_iff_surjective _).2 (hs n))
  exact cochainPullback_fst_quasiIso p.hom p.hom hq

include hs hq in
lemma endpointsTarget_quasiIso : QuasiIso (endpointsTarget R p).hom := by
  have : Epi p.hom := HomologicalComplex.epi_of_epi_f _
    (fun n => (ModuleCat.epi_iff_surjective _).2 (hs n))
  exact cochainPullback_snd_quasiIso p.hom p.hom hq

include hs hq in
lemma endpointsMap_quasiIso : QuasiIso (endpointsMap R p).hom := by
  have := endpointsSource_quasiIso R p hs hq
  have : QuasiIso ((endpointsMap R p).hom ≫ (endpointsSource R p).hom) := by
    change QuasiIso ((endpointsMap R p ≫ endpointsSource R p).hom)
    rw [endpointsMap_source]
    exact source_quasiIso R p hs hq
  exact quasiIso_of_comp_right (endpointsMap R p).hom (endpointsSource R p).hom

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativePath
