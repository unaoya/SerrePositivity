module

public import SerrePositivity.EInfinity.SimplexCuts.HorizontalFaceTerms
public import SerrePositivity.EInfinity.SimplexCuts.OutputBoundaryPairedValues

/-!
# BF全境界値の水平分岐

Berger–Fresse §1.2.3・§2.2.7、M14 L09a。
同じ係数の削除項と水平な出力項を、既存の全添字と共通次数で相殺する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- C221：正次数の係数の実境界項を、同じpositiveWordと指定切断で読む。 -/
lemma coefficientBoundaryTerm_succ_eq {r d q : ℕ} (S : SSet.{0})
    (u : Surjection.BasisWord (r + 1) (d + 1)) (c : Fin (r + d + 2) × Cut (r + d) q)
    (x : S _⦋q⦌)
    (h : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) = -(((d + 1) + q : ℕ) : ℤ) + 1) :
    coefficientBoundaryTerm A S r (d + 1) q u c x =
      if hw : Function.Surjective (Surjection.erase (positiveWord u).val c.1) ∧
          Surjection.Nondegenerate (Surjection.erase (positiveWord u).val c.1) then
        -Surjection.deletionCoefficient (positiveWord u).val c.1 •
          (eqToHom (congrArg (fun z : ℤ => (power (chains A S) (r + 1)).X z) h)).hom
            (cutTerm A S c.2 ⟨Surjection.erase (positiveWord u).val c.1, hw⟩ x)
      else 0 := by
  rfl

/-- C222：全境界値の係数分岐は、元の同じ係数境界項。 -/
lemma universalBoundaryValue_coefficient (S : SSet.{0}) {r d : ℕ}
    (u : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (c : Fin (r + d + 1) × Cut (r + d - 1) q) :
    universalBoundaryValue A S u q x (.inr (.inl c)) = coefficientBoundaryTerm A S r d q u c x := by
  rfl

/-- C223：正の係数次数の水平分岐は、全境界値で仮定なく相殺する。 -/
lemma universalBoundaryValue_horizontal_succ (S : SSet.{0}) {r d : ℕ}
    (u : Surjection.BasisWord (r + 1) (d + 1)) (q : ℕ) (x : S _⦋q⦌)
    (c : Fin (r + d + 2) × Cut (r + d) q) :
    universalBoundaryValue A S u q x (.inl (horizontalBoundaryFaceEquiv (r + d) q c).val) =
      -universalBoundaryValue A S u q x (.inr (.inl c)) := by
  let v := positiveWord u
  let z := horizontalBoundaryFaceEquiv (r + d) q c
  have ho : -((r + d + 1 + q + 1 - (r + 1) : ℕ) : ℤ) + 1 =
      -(((d + 1) + q : ℕ) : ℤ) + 1 := by omega
  have hc : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) =
      -(((d + 1) + q : ℕ) : ℤ) + 1 := by omega
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
  have hout := universalBoundaryValue_output_of_pair A S u q x z.val.1 z.val.2 ho
    ⟨label z.val.1 v.val z.val.2, j⟩ hp
  rw [Sigma.eta] at hout
  rw [universalBoundaryValue_coefficient, coefficientBoundaryTerm_succ_eq A S u c x hc, hout]
  by_cases hw : Function.Surjective (Surjection.erase v.val c.1) ∧
      Surjection.Nondegenerate (Surjection.erase v.val c.1)
  · rw [dite_eq_left hw]
    let w : Surjection.Word (r + 1) (r + d + 1) := ⟨Surjection.erase v.val c.1, hw⟩
    have ht := outputBoundaryTerm_horizontalBoundaryFaceEquiv_valid A S v w c rfl
      j hj x
    have ht' := congrArg (fun y =>
      (eqToHom (congrArg (fun n : ℤ => (power (chains A S) (r + 1)).X n) ho)).hom y) ht
    rw [map_zsmul] at ht'
    have step {M N P : ModuleCat.{u} A} (hMN : M = N) (hNP : N = P) (y : M) :
        (eqToHom hNP).hom ((eqToHom hMN).hom y) = (eqToHom (hMN.trans hNP)).hom y := by
      subst N
      subst P
      rfl
    rw [step] at ht'
    simp only [neg_smul, neg_neg]
    convert ht' using 1
  · rw [dite_eq_right hw]
    have ht := outputBoundaryTerm_horizontalBoundaryFaceEquiv_invalid A S v c hw
      j x
    have ht' := congrArg (fun y =>
      (eqToHom (congrArg (fun n : ℤ => (power (chains A S) (r + 1)).X n) ho)).hom y) ht
    simp only [map_zero] at ht'
    simp only [neg_zero]
    convert ht' using 1


/-- C224：既存の全水平同値によるhcは、係数次数零の場合も含め実境界値で成り立つ。 -/
lemma universalBoundaryValue_horizontal_neg (S : SSet.{0}) {r d : ℕ}
    (u : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌) (hm : 0 < r + d)
    (c : Fin (r + d + 1) × Cut (r + d - 1) q) :
    universalBoundaryValue A S u q x (.inl ((horizontalBoundaryAllEquiv (r + d) q hm) c).val) =
      -universalBoundaryValue A S u q x (.inr (.inl c)) := by
  cases d with
  | zero =>
    cases r with
    | zero => omega
    | succ r =>
      let v := positiveWord u
      let z := horizontalBoundaryFaceEquiv r q c
      have ho : -((r + 1 + q + 1 - (r + 2) : ℕ) : ℤ) + 1 =
          -((0 + q : ℕ) : ℤ) + 1 := by omega
      have hns : ¬(Function.Surjective (Surjection.erase v.val c.1) ∧
          Surjection.Nondegenerate (Surjection.erase v.val c.1)) := by
        intro hs
        have hcard := Fintype.card_le_of_surjective _ hs.1
        simp only [Fintype.card_fin] at hcard
        omega
      simp only [universalBoundaryValue_coefficient, coefficientBoundaryTerm, neg_zero]
      change universalBoundaryValue A S u q x (.inl z.val) = 0
      rcases hp : (colorPositionEquiv z.val.1 v).symm z.val.2 with ⟨a, j⟩
      have ha : a = label z.val.1 v.val z.val.2 := by
        have h := colorPositionEquiv_symm_color z.val.1 v z.val.2
        rw [hp] at h
        exact h
      subst a
      have ht := outputBoundaryTerm_horizontalBoundaryFaceEquiv_invalid A S v c hns j x
      have hout := universalBoundaryValue_output_of_pair A S u q x z.val.1 z.val.2 ho
        ⟨label z.val.1 v.val z.val.2, j⟩ hp
      rw [Sigma.eta] at hout
      rw [hout, ht, map_zero]
  | succ d =>
    exact universalBoundaryValue_horizontal_succ A S u q x c

end SerrePositivity.EInfinity.SimplexCuts
