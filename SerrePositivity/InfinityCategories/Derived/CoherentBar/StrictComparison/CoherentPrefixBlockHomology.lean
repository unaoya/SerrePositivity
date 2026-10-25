module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.SignedShiftBlockHomology
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstClosed

/-!
概要：元の coherent bar の一次 prefix ブロックのホモロジー係数。
方針：HA 辺の閉零係数から作る実加群射へ shift の符号相殺を適用する。
規約：元の prefix 係数と後尾ラベルを保持する。
使われ方：通常のホモロジー bar の零番の面との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open HomologicalComplex CochainComplex HomComplex
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarPrefixZeroHom_closed {n : ℕ} (s : I _⦋n + 1⦌) :
    (moduleHom R D (dgCoherentBarSource R D G ⟨n + 1, s⟩)
      (dgCoherentBarSource R D G (dgCoherentBarTail s 1 (by omega)))).d 0 1
        (dgCoherentBarPrefixHom R D G s 0 (by omega)) = 0 :=
  (dgCoherentBarPrefixHom_d R D G s 0 (by omega)).trans
    (dgCoherentBarPrefixBoundary_zero R D G s (by omega))

def dgCoherentBarSignedPrefixCochain {n : ℕ} (s : I _⦋n + 1⦌) (x : D) :
    Cochain ((moduleEvaluation R D x).obj (dgCoherentBarFamily R D G ⟨n + 1, s⟩))
      ((moduleEvaluation R D x).obj
        (dgCoherentBarFamily R D G (dgCoherentBarTail s 1 (by omega)))) 1 :=
  ((n : ℤ) + 1).negOnePow • (moduleHomπ R D
    (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D G ⟨n + 1, s⟩))
    (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D G
      (dgCoherentBarTail s 1 (by omega)))) x).f 1 (dgCoherentBarPrefixBlock R D G s 0 (by omega))

lemma dgCoherentBarSignedPrefixCochain_closed {n : ℕ} (s : I _⦋n + 1⦌) (x : D) :
    δ 1 2 (dgCoherentBarSignedPrefixCochain R D G s x) = 0 := by
  simpa only [dgCoherentBarSignedPrefixCochain, dgBarSignedShiftCochain,
    dgCoherentBarPrefixBlock, dgCoherentBarFamily, dgCoherentBarTail, Nat.add_sub_cancel,
    Nat.cast_add, Nat.cast_one] using!
    dgBarSignedShiftCochain_closed R D
      (M := ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D G ⟨n + 1, s⟩))
      (N := ForgetEnrichment.of (Complex R)
        (dgCoherentBarSource R D G (dgCoherentBarTail s 1 (by omega))))
      (dgCoherentBarPrefixHom R D G s 0 (by omega))
      (dgCoherentBarPrefixZeroHom_closed R D G s) (n : ℤ) x

lemma dgCoherentBarSignedPrefixHomology {n : ℕ} (s : I _⦋n + 1⦌) (x : D) (q : ℤ) :
    dgDegreeOneHomologyMap R (dgCoherentBarSignedPrefixCochain R D G s x)
      (dgCoherentBarSignedPrefixCochain_closed R D G s x) q ≫
      (dgComplexShiftHomologyIso R
        ((dgCoherentBarSource R D G (dgCoherentBarTail s 1 (by omega))).obj (Opposite.op x))
        (n : ℤ) (q + 1) (q + ((n : ℤ) + 1)) (by omega)).hom =
    (dgComplexShiftHomologyIso R
      ((dgCoherentBarSource R D G ⟨n + 1, s⟩).obj (Opposite.op x))
      ((n : ℤ) + 1) q (q + ((n : ℤ) + 1)) (by omega)).hom ≫
      HomologicalComplex.homologyMap ((moduleEvaluation R D x).map
        (moduleMorphismOfCycle R D
          (M := ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D G ⟨n + 1, s⟩))
          (N := ForgetEnrichment.of (Complex R)
            (dgCoherentBarSource R D G (dgCoherentBarTail s 1 (by omega))))
          (dgCoherentBarPrefixHom R D G s 0 (by omega))
          (dgCoherentBarPrefixZeroHom_closed R D G s))) (q + ((n : ℤ) + 1)) := by
  simpa only [dgCoherentBarSignedPrefixCochain, dgBarSignedShiftCochain,
    dgCoherentBarPrefixBlock, dgCoherentBarFamily, dgCoherentBarTail, Nat.add_sub_cancel,
    Nat.cast_add, Nat.cast_one] using!
    dgBarSignedShiftHomology R D
      (M := ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D G ⟨n + 1, s⟩))
      (N := ForgetEnrichment.of (Complex R)
        (dgCoherentBarSource R D G (dgCoherentBarTail s 1 (by omega))))
      (dgCoherentBarPrefixHom R D G s 0 (by omega))
      (dgCoherentBarPrefixZeroHom_closed R D G s) (n : ℤ) q x

end SerrePositivity.InfinityCategories
