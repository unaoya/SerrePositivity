module

public import SerrePositivity.InfinityCategories.DoldKanComparison.CubeBlockEvaluation
public import SerrePositivity.InfinityCategories.DoldKanComparison.CubeBlockPermutations
public import SerrePositivity.InfinityCategories.DoldKanComparison.AWDegenerate

/-!
# 連結した旗の AW 合成の最上位評価

概要：連結した旗における AW 合成の最上位評価は、各旗の最上位評価の dg 合成である。
方針：境目以外の切断項を退化によって消し、残る一項を評価する。
規約：両因子が零次元の場合も同じ式を使う。
使われ方：HA 1.3.1.16、Kerodon 2.5.8 の AW∘shuffle の各適合旗の計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DoldKanComparison
open CategoryTheory DifferentialGraded DGNerve.PinchedHom
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D] {x y z : D}

/-- 概要：連結した旗の境目以外の AW 切断項は零である。
方針：境目前は接尾の右射影、境目後は接頭の左射影に隣接頂点の重複を見つける。
規約：境目の頂点番号は p。
使われ方：Kerodon 2.5.8 の唯一の非退化な切断項への還元。 -/
lemma awTerm_cubeSum_zero_of_bad_cut {A B : Type u} {p q : ℕ}
    (e : Fin p ≃ A) (f : Fin q ≃ B)
    (ψ : Coherent.cube A ⟶ standardHomSpace (R := R) y z)
    (φ : Coherent.cube B ⟶ standardHomSpace (R := R) x y)
    (j : Fin (p + q + 1)) (hj : j.val ≠ p) (k : ℤ)
    (hk : k = 1 - ((Finset.univ : Finset (Fin (p + q + 1))).card : ℤ)) :
    awTerm (ψ.app _ ((cubeSumLeftMap A B).app _ (cubeFlag (cubeSumEnumeration e f)))).val
      (φ.app _ ((cubeSumRightMap A B).app _ (cubeFlag (cubeSumEnumeration e f)))).val
      Finset.univ ⟨j, Finset.mem_univ j⟩ k hk = 0 := by
  rcases lt_or_gt_of_ne hj with hj | hj
  · apply awTerm_nerve_zero_right
    let r : Fin p := ⟨j.val, hj⟩
    let t := Fin.castAdd q r
    intro hinj
    have h₀ : t.castSucc ∈ (Finset.univ : Finset (Fin (p + q + 1))).filter (j ≤ ·) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change j.val ≤ j.val; rfl⟩
    have h₁ : t.succ ∈ (Finset.univ : Finset (Fin (p + q + 1))).filter (j ≤ ·) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change j.val ≤ j.val + 1; omega⟩
    exact (ne_of_lt t.castSucc_lt_succ) (hinj h₀ h₁ (cubeSumRightMap_flag_repeat_left e f r))
  · apply awTerm_nerve_zero_left
    let r : Fin q := ⟨0, by have h := j.isLt; omega⟩
    let t := Fin.natAdd p r
    intro hinj
    have h₀ : t.castSucc ∈ (Finset.univ : Finset (Fin (p + q + 1))).filter (· ≤ j) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change p + 0 ≤ j.val; omega⟩
    have h₁ : t.succ ∈ (Finset.univ : Finset (Fin (p + q + 1))).filter (· ≤ j) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change p + 0 + 1 ≤ j.val; omega⟩
    exact (ne_of_lt t.castSucc_lt_succ) (hinj h₀ h₁ (cubeSumLeftMap_flag_repeat_right e f r))

/-- 概要：連結した旗の AW 合成の最上位評価は二つの旗の評価の dg 合成である。
方針：境目以外の項を消して、境目の一項の成分計算を適用する。
規約：後の射を先頭座標、前の射を末尾座標へ射影する。
使われ方：HA 1.3.1.16 の合成面の基本鎖の評価の各適合項。 -/
lemma standardTopEval_AW_cubeSum {A B : Type u} {p q : ℕ}
    (e : Fin p ≃ A) (f : Fin q ≃ B)
    (ψ : Coherent.cube A ⟶ standardHomSpace (R := R) y z)
    (φ : Coherent.cube B ⟶ standardHomSpace (R := R) x y) :
    standardTopEval (R := R) x z (p + q)
      (standardAW (ψ.app _ ((cubeSumLeftMap A B).app _ (cubeFlag (cubeSumEnumeration e f))))
        (φ.app _ ((cubeSumRightMap A B).app _ (cubeFlag (cubeSumEnumeration e f))))) =
      compose R (cubeFlagEvaluation e ψ) (cubeFlagEvaluation f φ) (by push_cast; omega) := by
  refine Eq.trans ?_ (awTerm_cubeSum_eq_comp e f ψ φ)
  change (awData (n := p + q) _ _).component Finset.univ (-((p + q : ℕ) : ℤ))
    Finset.univ_nonempty (by simp) = _
  rw [awData_component]
  apply Finset.sum_eq_single
    (⟨(⟨p, by omega⟩ : Fin (p + q + 1)), Finset.mem_univ _⟩ :
      (Finset.univ : Finset (Fin (p + q + 1))))
  · intro j _ hj
    exact awTerm_cubeSum_zero_of_bad_cut e f ψ φ j.val
      (fun h ↦ hj (Subtype.ext (Fin.ext h))) _ _
  · simp

/-- 概要：連結した全ての適合旗の AW 評価の符号付き和は二つの立方体評価の dg 合成である。
方針：各旗の AW 評価を dg 合成にし、区間内置換の二重和を分配してまとめる。
規約：全置換の和への拡張には不適合な旗の消去と再添字付けを別に使う。
使われ方：Kerodon 2.5.8 の AW∘shuffle の適合した全旗の寄与。 -/
lemma standardTopEval_AW_cubeSum_signed_sum {A B : Type u} {p q : ℕ}
    (e : Fin p ≃ A) (f : Fin q ≃ B)
    (ψ : Coherent.cube A ⟶ standardHomSpace (R := R) y z)
    (φ : Coherent.cube B ⟶ standardHomSpace (R := R) x y) :
    (∑ σ : Equiv.Perm (Fin p), ∑ τ : Equiv.Perm (Fin q),
      (Equiv.Perm.sign (cubeBlockPermutation σ τ) : ℤ) •
        standardTopEval (R := R) x z (p + q)
          (standardAW
            (ψ.app _ ((cubeSumLeftMap A B).app _
              (cubeFlag (cubeSumEnumeration (σ.trans e) (τ.trans f)))))
            (φ.app _ ((cubeSumRightMap A B).app _
              (cubeFlag (cubeSumEnumeration (σ.trans e) (τ.trans f))))))) =
      compose R (cubeEvaluation e ψ) (cubeEvaluation f φ) (by push_cast; omega) := by
  simp_rw [standardTopEval_AW_cubeSum]
  exact cubeBlockPermutation_signed_sum e f ψ φ

end SerrePositivity.InfinityCategories.DoldKanComparison
