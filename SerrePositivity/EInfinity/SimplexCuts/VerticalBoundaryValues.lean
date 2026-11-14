module

public import SerrePositivity.EInfinity.SimplexCuts.VerticalFaceTerms
public import SerrePositivity.EInfinity.SimplexCuts.OutputBoundaryPairedValues

/-!
# BF全境界値の垂直分岐

Berger–Fresse §2.2.7、M14 L09a。
同じ入力面の指定実境界値を、既存の全垂直添字の相殺へ戻す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- C252：全境界値の入力分岐は、元の同じ入力境界項。 -/
lemma universalBoundaryValue_input (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (c : Fin (q + 1) × Cut (r + d) (q - 1)) :
    universalBoundaryValue A S w q x (.inr (.inr c)) = simplexBoundaryTerm A S w q c x := by
  rfl

/-- C253：正の入力次数の垂直分岐は、元の全境界値で仮定なく相殺する。 -/
lemma universalBoundaryValue_vertical_succ (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q + 1⦌)
    (c : Fin (q + 2) × Cut (r + d) q) :
    universalBoundaryValue A S w (q + 1) x
        (.inl (verticalBoundaryFaceEquiv (r + d) q c).val) =
      -universalBoundaryValue A S w (q + 1) x (.inr (.inr c)) := by
  let v := positiveWord w
  let z := verticalBoundaryFaceEquiv (r + d) q c
  have ho : -((r + d + (q + 1) + 1 - (r + 1) : ℕ) : ℤ) + 1 =
      -((d + (q + 1) : ℕ) : ℤ) + 1 := by omega
  rcases hp : (colorPositionEquiv z.val.1 v).symm z.val.2 with ⟨a, j⟩
  have ha : a = label z.val.1 v.val z.val.2 := by
    have h := colorPositionEquiv_symm_color z.val.1 v z.val.2
    rw [hp] at h
    exact h
  subst a
  have hj : j.val = vertexRank z.val.1 v.val (label z.val.1 v.val z.val.2) z.val.2 := by
    have h := vertexRank_symm_colorPositionEquiv z.val.1 v z.val.2
    rw [hp] at h
    exact h.symm
  have hout := universalBoundaryValue_output_of_pair A S w (q + 1) x z.val.1 z.val.2 ho
    ⟨label z.val.1 v.val z.val.2, j⟩ hp
  rw [Sigma.eta] at hout
  have ht := outputBoundaryTerm_verticalBoundaryFaceEquiv A S v c j hj x
  have ht' := congrArg (fun y =>
    (eqToHom (congrArg (fun n : ℤ => (power (chains A S) (r + 1)).X n) ho)).hom y) ht
  rw [map_zsmul] at ht'
  have step {M N P : ModuleCat.{u} A} (hMN : M = N) (hNP : N = P) (y : M) :
      (eqToHom hNP).hom ((eqToHom hMN).hom y) = (eqToHom (hMN.trans hNP)).hom y := by
    subst N
    subst P
    rfl
  rw [step] at ht'
  have hdeg : r + d + 1 - (r + 1) = d := by omega
  rw [hdeg] at ht'
  rw [universalBoundaryValue_input, hout]
  simp only [simplexBoundaryTerm, neg_smul, neg_neg]
  convert ht' using 1

/-- C254：既存の全垂直同値によるhvは、全ての正の入力次数で成り立つ。 -/
lemma universalBoundaryValue_vertical_neg (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌) (hq : 0 < q)
    (c : Fin (q + 1) × Cut (r + d) (q - 1)) :
    universalBoundaryValue A S w q x
        (.inl ((verticalBoundaryAllEquiv (r + d) q hq) c).val) =
      -universalBoundaryValue A S w q x (.inr (.inr c)) := by
  cases q with
  | zero => omega
  | succ q => exact universalBoundaryValue_vertical_succ A S w q x c

end SerrePositivity.EInfinity.SimplexCuts
