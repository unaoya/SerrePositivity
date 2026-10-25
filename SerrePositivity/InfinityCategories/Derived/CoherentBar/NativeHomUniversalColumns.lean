module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeHomComposition
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeCocone
/-!
概要：native 成分への後合成は全次数 Hom と非退化成分族の間の全単射である。
方針：実際の後合成を正規化 Hom の線形同値に同定し、その逆を使う。
規約：成分族の閉性は元の theta の明示的微分で判定する。native 余極限判定は別工程。
使われ方：工程Bの逆写像と全 Hom 普遍性の代数的入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

lemma dgCoherentBarNativeHomUniversalColumns (q : ℤ) :
    Function.Bijective (fun z :
      (moduleHom R D (dgCoherentBarNormalizedModule R D F hMC) N).X q =>
      fun s : dgCoherentBarNormalizedIndex I =>
        compose R (x := dgCoherentBarSource R D F s.val)
          (y := dgCoherentBarNormalizedModule R D F hMC) (z := N) z
          (dgCoherentBarNativeColumn R D F hMC s.val)
          (show -(s.val.1 : ℤ) + q = q - (s.val.1 : ℤ) by omega)) := by
  have hfun : (fun z : (moduleHom R D (dgCoherentBarNormalizedModule R D F hMC) N).X q =>
      fun s : dgCoherentBarNormalizedIndex I =>
        compose R (x := dgCoherentBarSource R D F s.val)
          (y := dgCoherentBarNormalizedModule R D F hMC) (z := N) z
          (dgCoherentBarNativeColumn R D F hMC s.val)
          (show -(s.val.1 : ℤ) + q = q - (s.val.1 : ℤ) by omega)) =
      dgCoherentBarNormalizedNativeHomEquiv R D F hMC N q := by
    funext z s
    exact dgCoherentBarNativeColumn_compose_eq_coordinates R D F hMC N q z s
  rw [hfun]
  exact (dgCoherentBarNormalizedNativeHomEquiv R D F hMC N q).bijective

lemma dgCoherentBarNativeHomUniversalColumns_closed_iff (q : ℤ)
    (z : (moduleHom R D (dgCoherentBarNormalizedModule R D F hMC) N).X q) :
    (moduleHom R D (dgCoherentBarNormalizedModule R D F hMC) N).d q (q + 1) z = 0 ↔
    dgCoherentBarNormalizedNativeHomDifferential R D F N q
      (dgCoherentBarNormalizedNativeHomEquiv R D F hMC N q z) = 0 := by
  rw [← dgCoherentBarNormalizedNativeHomEquiv_d]
  exact (dgCoherentBarNormalizedNativeHomEquiv R D F hMC N (q + 1)).map_eq_zero_iff.symm

def dgCoherentBarNativeClosedHomEquiv (q : ℤ) :
    {z : (moduleHom R D (dgCoherentBarNormalizedModule R D F hMC) N).X q //
      (moduleHom R D (dgCoherentBarNormalizedModule R D F hMC) N).d q (q + 1) z = 0} ≃
    {a : ∀ s : dgCoherentBarNormalizedIndex I,
      (moduleHom R D (dgCoherentBarSource R D F s.val) N).X (q - (s.val.1 : ℤ)) //
      dgCoherentBarNormalizedNativeHomDifferential R D F N q a = 0} :=
  (dgCoherentBarNormalizedNativeHomEquiv R D F hMC N q).toEquiv.subtypeEquiv
    (dgCoherentBarNativeHomUniversalColumns_closed_iff R D F hMC N q)

lemma dgCoherentBarNativeHomUniversalColumns_unconditional (q : ℤ) :
    Function.Bijective (fun z :
      (moduleHom R D
        (dgCoherentBarNormalizedModule R D F (dgCoherentBarTheta_maurerCartan R D F)) N).X q =>
      fun s : dgCoherentBarNormalizedIndex I =>
        compose R (x := dgCoherentBarSource R D F s.val)
          (y := dgCoherentBarNormalizedModule R D F (dgCoherentBarTheta_maurerCartan R D F))
          (z := N) z (dgCoherentBarNativeColumn R D F
            (dgCoherentBarTheta_maurerCartan R D F) s.val)
          (show -(s.val.1 : ℤ) + q = q - (s.val.1 : ℤ) by omega)) :=
  dgCoherentBarNativeHomUniversalColumns R D F (dgCoherentBarTheta_maurerCartan R D F) N q

end SerrePositivity.InfinityCategories
