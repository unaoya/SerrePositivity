module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.LaxTensorComparison
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Insertion

/-!
# オペラッド代数のテンソル構造の比較

## 概要
Berger–Moerdijk §1 の置換と一箇所への代入を、lax braided 関手の下で比較する。

## 方針
置換を隣接交換で生成し、代入の構造射ごとの比較を順に合成する。

## 規約
代入する演算の係数の比較射は任意で、零入力を含める。

## 使われ方
Barratt–Eccles の代数作用を環準同型に沿って制限する。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory TensorPowers
open SerrePositivity.Coxeter

section Permutation

variable {C D : Type*} [Category* C] [MonoidalCategory C] [SymmetricCategory C]
  [Category* D] [MonoidalCategory D] [SymmetricCategory D]
  (F : C ⥤ D) [F.LaxBraided]

/-- 一因子を固定したテンソル冪の比較を再帰式に戻す。 -/
lemma laxTensorComparison_id_power (X : C) (n : ℕ) :
    laxTensorComparison F (𝟙 (F.obj X)) (laxPowerComparison F X n) =
      laxPowerComparison F X (n + 1) := by
  rw [laxTensorComparison, id_tensorHom, laxPowerComparison]

/-- 最初の二因子の交換とテンソル冪の比較の可換性。 -/
lemma laxPowerComparison_swapFirst (X : C) (n : ℕ) :
    LaxComparisonSquare F (laxPowerComparison F X (n + 2)) (laxPowerComparison F X (n + 2))
      (swapFirstIso (F.obj X) n).hom (swapFirstIso X n).hom := by
  let e := 𝟙 (F.obj X)
  let p := laxPowerComparison F X n
  have h := LaxComparisonSquare.associator F e e p
  have k := LaxComparisonSquare.whiskerRight F p (LaxComparisonSquare.braiding F e e)
  have h' := LaxComparisonSquare.comp F (LaxComparisonSquare.iso_inv F h)
    (LaxComparisonSquare.comp F k h)
  simp only [e, p, laxTensorComparison_id_power] at h'
  simpa only [swapFirstIso, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, Category.assoc]
    using h'

/-- 隣接する任意の二因子の交換とテンソル冪の比較の可換性。 -/
lemma laxPowerComparison_adjacent (X : C) (n : ℕ) (i : Fin n) :
    LaxComparisonSquare F (laxPowerComparison F X (n + 1)) (laxPowerComparison F X (n + 1))
      (adjacentIso (F.obj X) n i).hom (adjacentIso X n i).hom := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · exact laxPowerComparison_swapFirst F X n
    · have h := LaxComparisonSquare.whiskerLeft F (𝟙 (F.obj X)) (ih i)
      simpa only [laxTensorComparison_id_power, adjacentIso, Fin.cases_succ,
        whiskerLeftIso_hom] using h

/-- 入力の置換とテンソル冪の比較の可換性。 -/
lemma laxPowerComparison_permutation (X : C) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    LaxComparisonSquare F (laxPowerComparison F X n) (laxPowerComparison F X n)
      (permutationAction (F.obj X) n σ).asIso.hom (permutationAction X n σ).asIso.hom := by
  cases n with
  | zero =>
    simpa only [permutationAction_zero] using LaxComparisonSquare.id F (laxPowerComparison F X 0)
  | succ n =>
    apply permutation_induction_right σ
    · simpa only [permutationAction_one] using
        LaxComparisonSquare.id F (laxPowerComparison F X (n + 1))
    · intro τ i ih
      simpa only [permutationAction_mul, permutationAction_adjacent, adjacentAut] using
        LaxComparisonSquare.comp F (laxPowerComparison_adjacent F X n i) ih

end Permutation

section Insertion

open DifferentialGraded

variable {S T : Type u} [CommRing S] [CommRing T]
  (F : Complex T ⥤ Complex S) [F.LaxBraided]

/-- tensorator と比較写像は、一箇所へ演算を代入する構造射と可換。 -/
lemma laxPowerComparison_insertion (K C : Complex T) (C' : Complex S)
    (c : C' ⟶ F.obj C) (m n : ℕ) (i : Fin (m + 1))
    (θ : C ⊗ power K n ⟶ K) :
    LaxComparisonSquare F
      (laxTensorComparison F c (laxPowerComparison F K (m + n)))
      (laxPowerComparison F K (m + 1))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction (F.obj K) C' m n i
        (laxTensorComparison F c (laxPowerComparison F K n) ≫ F.map θ))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction K C m n i θ) := by
  let p := laxPowerComparison F K
  let s := i.val
  let t := m - s
  have e₁ : m + n = s + (n + t) := by dsimp [s, t]; omega
  have e₂ : s + (t + 1) = m + 1 := by dsimp [s, t]; omega
  have hIndex {a b : ℕ} (e : a = b) :
      LaxComparisonSquare F (p a) (p b)
        (eqToHom (congrArg (power (F.obj K)) e)) (eqToHom (congrArg (power K) e)) :=
    laxPowerComparison_index F K e
  have hAppend (a b : ℕ) :
      LaxComparisonSquare F (laxTensorComparison F (p a) (p b)) (p (a + b))
        (appendIso (F.obj K) a b).hom (appendIso K a b).hom :=
    (laxPowerComparison_append F K a b).symm
  have hθ : LaxComparisonSquare F (laxTensorComparison F c (p n)) (𝟙 (F.obj K))
      (laxTensorComparison F c (p n) ≫ F.map θ) θ := by
    exact Category.comp_id _
  let h₁ := LaxComparisonSquare.whiskerLeft F c
    (LaxComparisonSquare.comp F (hIndex e₁)
      (LaxComparisonSquare.iso_inv F (hAppend s (n + t))))
  let h₂ := LaxComparisonSquare.iso_inv F (LaxComparisonSquare.associator F c (p s) (p (n + t)))
  let h₃ := LaxComparisonSquare.whiskerRight F (p (n + t))
    (LaxComparisonSquare.braiding F c (p s))
  let h₄ := LaxComparisonSquare.associator F (p s) c (p (n + t))
  let h₅ := LaxComparisonSquare.whiskerLeft F (p s)
    (LaxComparisonSquare.whiskerLeft F c (LaxComparisonSquare.iso_inv F (hAppend n t)))
  let h₆ := LaxComparisonSquare.whiskerLeft F (p s)
    (LaxComparisonSquare.iso_inv F (LaxComparisonSquare.associator F c (p n) (p t)))
  have h₇ := LaxComparisonSquare.whiskerLeft F (p s) (LaxComparisonSquare.whiskerRight F (p t) hθ)
  rw [show laxTensorComparison F (𝟙 (F.obj K)) (p t) = p (t + 1) from
    laxTensorComparison_id_power F K t] at h₇
  exact LaxComparisonSquare.comp F h₁
    (LaxComparisonSquare.comp F h₂
      (LaxComparisonSquare.comp F h₃
        (LaxComparisonSquare.comp F h₄
          (LaxComparisonSquare.comp F h₅
            (LaxComparisonSquare.comp F h₆
              (LaxComparisonSquare.comp F h₇
                (LaxComparisonSquare.comp F (hAppend s (t + 1)) (hIndex e₂))))))))

end Insertion

end SerrePositivity.EInfinity
