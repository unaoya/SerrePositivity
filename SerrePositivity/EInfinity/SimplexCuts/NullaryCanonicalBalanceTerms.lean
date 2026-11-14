module

public import SerrePositivity.EInfinity.SimplexCuts.MatchedSubsetPairing
public import SerrePositivity.EInfinity.SimplexCuts.NullaryCochainCutSums

/-!
# 元の空語Cut対応の全添字と符号付き実項

Berger–Fresse §2.2.6、M14 L12a、報告 §372。
元の小さい全Cutと、零項も含む元の大きい全Cutを直和で保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped Simplicial

/-- 元の小さいCutの同じ符号付き実テンソル（BF §2.2.6）。 -/
def nullarySmallCutTerm (A : Type u) [CommRing A] (S : SSet.{0}) {m q r : ℕ}
    (w : Surjection.Word r (m + 1)) (x : S _⦋q⦌) (z : ℤ)
    (hz : -((m + q + 1 - r : ℕ) : ℤ) = z) (t : Cut m q) : (power (chains A S) r).X z :=
  cutSign t w.val • vectorTensorAt (chains A S) r (cutGeneratorFamily A S t w x) z
    (by rw [vectorDegree_cutGeneratorFamily]; exact hz)

/-- 元の大きいCutの符号と実際の空語代入の値（BF §2.2.6）。 -/
def nullaryOuterCutTerm (A : Type u) [CommRing A] (S : SSet.{0}) {m q r : ℕ}
    (v : Surjection.Word (r + 1) (m + 2)) (ν : Surjection.BasisWord 0 0) (k : Fin (r + 1))
    (x : S _⦋q⦌) (z : ℤ) (hz : -((m + q + 1 - r : ℕ) : ℤ) = z)
    (s : Cut (m + 1) q) : (power (chains A S) r).X z :=
  cutSign s v.val •
    (tensorCoInsertionAction (chains A S) (Surjection.complex A 0) r 0 k
      (cochainAction A S 0)).f z
      (ιTensorObj (Surjection.complex A 0) (power (chains A S) (r + 1)) 0 z z (zero_add z)
        ((Surjection.complexXIso A 0 0).inv (Surjection.basis A 0 0 (ULift.up ν)) ⊗ₜ[A]
          vectorTensorAt (chains A S) (r + 1) (cutGeneratorFamily A S s v x) z
            (by rw [vectorDegree_cutGeneratorFamily]
                have h : (m + 1) + q + 1 - (r + 1) = m + q + 1 - r := by omega
                rwa [h])))

/-- 元の一点挿入の対応だけを交換し、正次数の右の零項を固定する（BF §2.2.6）。 -/
def nullaryCanonicalBalancePerm {m q r : ℕ} (v : Surjection.Word r (m + 2))
    (p : Fin (m + 2)) (k : Fin r) (hp : v.val p = k) (hu : ∀ j, v.val j = k → j = p) :
    Equiv.Perm (Cut m q ⊕ Cut (m + 1) q) :=
  matchedSubsetPerm (fun s : Cut (m + 1) q => outputDegree s v k = 0)
    (nullaryOutputCutEquiv m q r v p k hp hu)

/-- 元の全Cutの左項と、負号付きの実際の全右項（BF §2.2.6）。 -/
def nullaryCanonicalBalanceTerm (A : Type u) [CommRing A] (S : SSet.{0}) {m q r : ℕ}
    (v : Surjection.Word (r + 1) (m + 2)) (w : Surjection.Word r (m + 1))
    (ν : Surjection.BasisWord 0 0) (k : Fin (r + 1)) (x : S _⦋q⦌) (z : ℤ)
    (hz : -((m + q + 1 - r : ℕ) : ℤ) = z) :
    Cut m q ⊕ Cut (m + 1) q → (power (chains A S) r).X z :=
  matchedSubsetBalanceTerm (nullarySmallCutTerm A S w x z hz)
    (nullaryOuterCutTerm A S v ν k x z hz)

end SerrePositivity.EInfinity.SimplexCuts
