module

public import SerrePositivity.Asymptotic.SupportedKaroubi
public import SerrePositivity.CategoryTheory.Karoubi.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-! # 支持部分圏の比較と完全三角形の両立 -/

@[expose] public section

universe u

set_option synthInstance.maxSize 1024

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Idempotents

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ}
  {e : ℕ} (z : Fin e → R)

noncomputable instance supportedKaroubiFunctor_commShift :
    (supportedKaroubiFunctor (s := s) z).CommShift ℤ := by
  dsimp only [supportedKaroubiFunctor]
  infer_instance

instance supportedKaroubiFunctor_isTriangulated :
    (supportedKaroubiFunctor (s := s) z).IsTriangulated := by
  let P := supportedCompletedRankQuotient (s := s) z
  let F := (functorExtension₂ _ _).obj (supportedRankQuotientInclusion (s := s) z)
  exact (Functor.isTriangulated_iff_comp_right (P.liftCompιIso F (supportedKaroubi_image z))).mpr
    inferInstance

noncomputable instance supportedKaroubiEquivalence_functor_commShift :
    (supportedKaroubiEquivalence (s := s) z).functor.CommShift ℤ :=
  supportedKaroubiFunctor_commShift z

noncomputable instance supportedKaroubiEquivalence_inverse_commShift :
    (supportedKaroubiEquivalence (s := s) z).inverse.CommShift ℤ :=
  (supportedKaroubiEquivalence z).commShiftInverse ℤ

instance supportedKaroubiEquivalence_commShift :
    (supportedKaroubiEquivalence (s := s) z).CommShift ℤ :=
  (supportedKaroubiEquivalence z).commShift_of_functor ℤ

instance supportedKaroubiEquivalence_functor_isTriangulated :
    (supportedKaroubiEquivalence (s := s) z).functor.IsTriangulated :=
  supportedKaroubiFunctor_isTriangulated z

instance supportedKaroubiEquivalence_isTriangulated :
    (supportedKaroubiEquivalence (s := s) z).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ inferInstance

end SerrePositivity.Asymptotic
