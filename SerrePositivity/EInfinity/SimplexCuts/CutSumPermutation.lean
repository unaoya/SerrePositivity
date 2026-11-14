module

public import SerrePositivity.EInfinity.SimplexCuts.CutTermPermutation
public import SerrePositivity.EInfinity.SimplexCuts.RawAction

/-!
# 同じ一般切断和の置換の法則

Berger–Fresse §2.2.6、M14 L11。
元の切断項の置換と、元の語長・全次数の等式移送を同じ有限和で比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory HomologicalComplex
open SerrePositivity.TensorPowers
open scoped Simplicial

/-- C342：同じ語長の移送は、元の色置換と可換（BF §1.2.1）。 -/
lemma rename_eq_mp {n l l' : ℕ} (h : l = l') (σ : Equiv.Perm (Fin n))
    (v : Surjection.Word n l) :
    Eq.mp (congrArg (fun k => Surjection.Word n k) h) (Surjection.Word.rename σ v) =
      Surjection.Word.rename σ (Eq.mp (congrArg (fun k => Surjection.Word n k) h) v) := by
  subst l'
  rfl

/-- C343：切断用に語長を読む同じpositiveWordは、色置換と可換（BF §2.2.6）。 -/
lemma positiveWord_rename {r d : ℕ} (v : Surjection.BasisWord (r + 1) d)
    (σ : Equiv.Perm (Fin (r + 1))) :
    positiveWord (Surjection.Word.rename σ v) = Surjection.Word.rename σ (positiveWord v) := by
  unfold positiveWord
  exact rename_eq_mp (by omega) σ v

variable (A : Type u) [CommRing A]

/-- L11：同じ切断和の色置換は、元の実テンソルのKoszul置換（BF §2.2.6）。 -/
lemma cutSum_permutation (S : SSet.{0}) {r d q : ℕ}
    (v : Surjection.BasisWord (r + 1) d) (σ : Equiv.Perm (Fin (r + 1))) (x : S _⦋q⦌) :
    cutSum A S (Surjection.Word.rename σ v) x =
      (permutationAction (chains A S) (r + 1) σ).asIso.hom.f (-((d + q : ℕ) : ℤ))
        (cutSum A S v x) := by
  symm
  unfold cutSum
  rw [component_index_naturality A]
  · simp only [map_sum, cutTerm_permutation, positiveWord_rename]
  · congr 1
    congr 1
    omega

end SerrePositivity.EInfinity.SimplexCuts
