module

public import SerrePositivity.InfinityCategories.DoldKanComparison.CubeSumFlags
public import SerrePositivity.InfinityCategories.DoldKanComparison.DegenerateEvaluation

/-!
# 連結した旗の境目の AW 項の評価

概要：連結した旗の境目の一項は二つの元の旗の最上位評価の dg 合成である。
方針：接頭・接尾の像の成分を単射な引き戻しの最上位評価へ移し、元の旗と同定する。
規約：左の座標が後の射、右の座標が前の射で、合成の次数は −(p+q)。
使われ方：HA 1.3.1.16、Kerodon 2.5.8 の AW∘shuffle の残る一項。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DoldKanComparison
open CategoryTheory DifferentialGraded DGNerve.PinchedHom
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D] {x y z : D}

/-- 概要：連結した旗の左射影の接頭成分は元の左の旗の最上位評価である。
方針：接頭包含の像に沿う成分計算と単体集合の射の自然性を使う。
規約：次数 k を濃度で指定し、−p との同定を異種等号で表す。
使われ方：HA 1.3.1.16 の AW の後の射の成分の計算。 -/
lemma standardComponent_cubeSum_prefix {A B : Type u} {p q : ℕ}
    (e : Fin p ≃ A) (f : Fin q ≃ B)
    (ψ : Coherent.cube A ⟶ standardHomSpace (R := R) y z) (k : ℤ)
    (hk : k = 1 - (((Finset.univ : Finset (Fin (p + q + 1))).filter
      (· ≤ (⟨p, by omega⟩ : Fin (p + q + 1)))).card : ℤ)) :
    HEq ((ψ.app _ ((cubeSumLeftMap A B).app _ (cubeFlag (cubeSumEnumeration e f)))).val.component
      ((Finset.univ : Finset (Fin (p + q + 1))).filter (· ≤ (⟨p, by omega⟩ : Fin (p + q + 1)))) k
      (AWIndex.left_nonempty (Finset.mem_univ (⟨p, by omega⟩ : Fin (p + q + 1)))) hk)
      (cubeFlagEvaluation e ψ) := by
  have hp : k = -(p : ℤ) := by rw [cubePrefixOrder_card] at hk; omega
  subst hp
  have ht := standardTopEval_pullback_injective (cubePrefixOrder p q)
    (ψ.app _ ((cubeSumLeftMap A B).app _ (cubeFlag (cubeSumEnumeration e f))))
    (cubePrefixOrder_injective p q)
  simp only [cubePrefixOrder_image_univ] at ht
  apply heq_of_eq
  refine ht.symm.trans ?_
  refine (congrArg (standardTopEval (R := R) y z p)
    (ψ.naturality_apply (SimplexCategory.mkHom (cubePrefixOrder p q)).op
      ((cubeSumLeftMap A B).app _ (cubeFlag (cubeSumEnumeration e f)))).symm).trans ?_
  rw [cubeSumLeftMap_flag_prefix]
  rfl

/-- 概要：連結した旗の右射影の接尾成分は元の右の旗の最上位評価である。
方針：接尾包含の像に沿う成分計算と単体集合の射の自然性を使う。
規約：次数 k を濃度で指定し、−q との同定を異種等号で表す。
使われ方：HA 1.3.1.16 の AW の前の射の成分の計算。 -/
lemma standardComponent_cubeSum_suffix {A B : Type u} {p q : ℕ}
    (e : Fin p ≃ A) (f : Fin q ≃ B)
    (φ : Coherent.cube B ⟶ standardHomSpace (R := R) x y) (k : ℤ)
    (hk : k = 1 - (((Finset.univ : Finset (Fin (p + q + 1))).filter
      ((⟨p, by omega⟩ : Fin (p + q + 1)) ≤ ·)).card : ℤ)) :
    HEq ((φ.app _ ((cubeSumRightMap A B).app _ (cubeFlag (cubeSumEnumeration e f)))).val.component
      ((Finset.univ : Finset (Fin (p + q + 1))).filter ((⟨p, by omega⟩ : Fin (p + q + 1)) ≤ ·)) k
      (AWIndex.right_nonempty (Finset.mem_univ (⟨p, by omega⟩ : Fin (p + q + 1)))) hk)
      (cubeFlagEvaluation f φ) := by
  have hp : k = -(q : ℤ) := by rw [cubeSuffixOrder_card] at hk; omega
  subst hp
  have ht := standardTopEval_pullback_injective (cubeSuffixOrder p q)
    (φ.app _ ((cubeSumRightMap A B).app _ (cubeFlag (cubeSumEnumeration e f))))
    (cubeSuffixOrder_injective p q)
  simp only [cubeSuffixOrder_image_univ] at ht
  apply heq_of_eq
  refine ht.symm.trans ?_
  refine (congrArg (standardTopEval (R := R) x y q)
    (φ.naturality_apply (SimplexCategory.mkHom (cubeSuffixOrder p q)).op
      ((cubeSumRightMap A B).app _ (cubeFlag (cubeSumEnumeration e f)))).symm).trans ?_
  rw [cubeSumRightMap_flag_suffix]
  rfl

/-- 概要：境目の AW 項は元の二つの旗の最上位評価の dg 合成である。
方針：両成分の異種等号と次数の濃度計算を通常順合成へ移す。
規約：任意の p,q を扱い、どちらかが零の場合も含む。
使われ方：Kerodon 2.5.8 の AW∘shuffle の唯一の非零項の評価。 -/
lemma awTerm_cubeSum_eq_comp {A B : Type u} {p q : ℕ}
    (e : Fin p ≃ A) (f : Fin q ≃ B)
    (ψ : Coherent.cube A ⟶ standardHomSpace (R := R) y z)
    (φ : Coherent.cube B ⟶ standardHomSpace (R := R) x y) :
    awTerm (ψ.app _ ((cubeSumLeftMap A B).app _ (cubeFlag (cubeSumEnumeration e f)))).val
      (φ.app _ ((cubeSumRightMap A B).app _ (cubeFlag (cubeSumEnumeration e f)))).val
      Finset.univ ⟨(⟨p, by omega⟩ : Fin (p + q + 1)), Finset.mem_univ _⟩
      (-((p + q : ℕ) : ℤ)) (by simp) =
      compose R (cubeFlagEvaluation e ψ) (cubeFlagEvaluation f φ) (by push_cast; omega) := by
  unfold awTerm
  apply compose_eq_of_heq
  · exact standardComponent_cubeSum_prefix e f ψ _ _
  · exact standardComponent_cubeSum_suffix e f φ _ _
  · rw [cubeSuffixOrder_card]
    push_cast
    omega
  · rw [cubePrefixOrder_card]
    push_cast
    omega

end SerrePositivity.InfinityCategories.DoldKanComparison
