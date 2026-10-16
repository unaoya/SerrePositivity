module
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex

/-! # 閉じた二乗零cochainによる非有界複体の微分の変更

次数+1のcochain θについてδθ=0とθ²=0を個別の証明として受け取り、d+θを微分とする。
dg商への適用ではθ²=0を別途証明する必要がある。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] (K : Complex A) (θ : Cochain K K 1)

/-- 閉じた次数+1の自己cochainは元の微分と反交換する。 -/
lemma closed_one_anticommute (hθ : δ 1 2 θ = 0) (i : ℤ) :
    θ.v i (i + 1) rfl ≫ K.d (i + 1) (i + 1 + 1) +
      K.d i (i + 1) ≫ θ.v (i + 1) (i + 1 + 1) rfl = 0 := by
  have h := congrArg (fun f : Cochain K K 2 => f.v i (i + 1 + 1) (by omega)) hθ
  rw [δ_v 1 2 (by omega) θ i (i + 1 + 1) (by omega) (i + 1) (i + 1)
    (by omega) rfl, show (2 : ℤ).negOnePow = 1 by decide, one_smul, Cochain.zero_v] at h
  exact h

/-- cochainの二乗零から隣接する成分の合成零を得る。 -/
lemma square_zero_one_components
    (hθθ : θ.comp θ (show (1 : ℤ) + 1 = 2 by omega) = 0) (i : ℤ) :
    θ.v i (i + 1) rfl ≫ θ.v (i + 1) (i + 1 + 1) rfl = 0 := by
  have h := congrArg (fun f : Cochain K K 2 => f.v i (i + 1 + 1) (by omega)) hθθ
  rw [Cochain.comp_v θ θ _ i (i + 1) (i + 1 + 1) rfl rfl, Cochain.zero_v] at h
  exact h

/-- 元の微分と閉じた二乗零作用素の和も二乗零。 -/
lemma perturbedDifferential_squared (hθ : δ 1 2 θ = 0)
    (hθθ : θ.comp θ (show (1 : ℤ) + 1 = 2 by omega) = 0) (i : ℤ) :
    (K.d i (i + 1) + θ.v i (i + 1) rfl) ≫
      (K.d (i + 1) (i + 1 + 1) + θ.v (i + 1) (i + 1 + 1) rfl) = 0 := by
  rw [add_comp, comp_add, comp_add, K.d_comp_d, zero_add,
    square_zero_one_components K θ hθθ, add_zero]
  exact (add_comm _ _).trans (closed_one_anticommute K θ hθ i)

/-- 各次数の加群を保ち、微分をd+θへ変更した非有界複体。 -/
def perturbComplex (hθ : δ 1 2 θ = 0)
    (hθθ : θ.comp θ (show (1 : ℤ) + 1 = 2 by omega) = 0) : Complex A :=
  CochainComplex.of K.X (fun i => K.d i (i + 1) + θ.v i (i + 1) rfl)
    (perturbedDifferential_squared K θ hθ hθθ)

@[simp] lemma perturbComplex_X (hθ : δ 1 2 θ = 0)
    (hθθ : θ.comp θ (show (1 : ℤ) + 1 = 2 by omega) = 0) (i : ℤ) :
    (perturbComplex K θ hθ hθθ).X i = K.X i := rfl

@[simp] lemma perturbComplex_d (hθ : δ 1 2 θ = 0)
    (hθθ : θ.comp θ (show (1 : ℤ) + 1 = 2 by omega) = 0) (i : ℤ) :
    (perturbComplex K θ hθ hθθ).d i (i + 1) =
      K.d i (i + 1) + θ.v i (i + 1) rfl := by
  exact CochainComplex.of_d K.X (fun j => K.d j (j + 1) + θ.v j (j + 1) rfl) i

end SerrePositivity.DifferentialGraded
