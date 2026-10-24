module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackProjectionAt
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovConnectivity

/-!
概要：有限切断商に沿う実 pullback の左射影を、切断範囲の全次数で準同型比較する。
方針：切断商の全次数のホモロジー全射性と、切断範囲の同型性を使う。
規約：源の高次数群の消滅は要求しない。使われ方：未切断の連結なレベル表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (cutoff : ℤ)

lemma postnikovQuotient_quasiIsoAt (z : ℤ) (hz : -cutoff ≤ z) :
    QuasiIsoAt (postnikovQuotient R B cutoff).hom z := by
  change QuasiIsoAt (B.X.πTruncGE (-cutoff)) z
  exact CochainComplex.quasiIsoAt_πTruncGE B.X (-cutoff) z hz

lemma postnikovQuotient_homology_epi (z : ℤ) :
    Epi (homologyMap (postnikovQuotient R B cutoff).hom z) := by
  by_cases hz : -cutoff ≤ z
  · have : IsIso (homologyMap (postnikovQuotient R B cutoff).hom z) :=
      (quasiIsoAt_iff_isIso_homologyMap _ _).1 (postnikovQuotient_quasiIsoAt R B cutoff z hz)
    infer_instance
  · have : (postnikov R B cutoff).X.IsStrictlyGE (-cutoff) :=
      postnikovComplex_lowerBound R B cutoff
    have hzero := (postnikov R B cutoff).X.isZero_of_isGE (-cutoff) z (by omega)
    have : Subsingleton ((postnikov R B cutoff).X.homology z) :=
      (ModuleCat.isZero_iff_subsingleton).1 hzero
    apply (ModuleCat.epi_iff_surjective _).2
    exact Function.surjective_to_subsingleton _

lemma homotopyPullback_postnikov_left_quasiIsoAt {M : Mon (Complex R)}
    (f : M ⟶ postnikov R B cutoff) (z : ℤ) (hz : -cutoff ≤ z) :
    QuasiIsoAt (HomotopyPullbackModel.left R f (postnikovQuotient R B cutoff)).hom z :=
  HomotopyPullbackModel.left_quasiIsoAt_of_epi R f (postnikovQuotient R B cutoff) z
    (postnikovQuotient_homology_epi R B cutoff (z - 1))
    (postnikovQuotient_quasiIsoAt R B cutoff z hz)

lemma postnikovQuotient_connected_succ :
    IsConnected R (postnikovQuotient R B cutoff) (cutoff + 1) := by
  refine ⟨fun j hj => (postnikovQuotient_groups_bijective R B cutoff j (by omega)).1, ?_⟩
  intro j hj
  by_cases h : j ≤ cutoff
  · exact (postnikovQuotient_groups_bijective R B cutoff j h).2
  · have := postnikov_groups_subsingleton R B cutoff j (by omega)
    exact Function.surjective_to_subsingleton _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
