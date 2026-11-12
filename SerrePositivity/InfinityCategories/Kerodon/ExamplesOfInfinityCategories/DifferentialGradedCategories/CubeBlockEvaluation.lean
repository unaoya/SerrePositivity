module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeSumFlags
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DegenerateEvaluation

/-!
# 連結した旗の境目の AW 項の評価

概要：連結した旗の境目の一項は二つの元の旗の最上位評価の dg 合成である。
方針：接頭・接尾の像の成分を単射な引き戻しの最上位評価へ移し、元の旗と同定する。
規約：左の座標が後の射、右の座標が前の射で、合成の次数は −(p+q)。
使われ方：HA 1.3.1.16、Kerodon 2.5.8（Tag 00S0） の AW∘shuffle の残る一項。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y z : D}

/-- 概要：連結した旗の左射影の接頭成分は元の左の旗の最上位評価である。
方針：接頭包含の像に沿う成分計算と単体集合の射の自然性を使う。
規約：次数 k を濃度で指定し、−p との同定を異種等号で表す。
使われ方：HA 1.3.1.16 の AW の後の射の成分の計算。 -/
lemma standardComponent_cubeSum_prefix {A B : Type u} {p q : ℕ}
    (e : Fin p ≃ A) (f : Fin q ≃ B)
    (ψ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) y z) (k : ℤ)
    (hk : k = 1 - (((Finset.univ : Finset (Fin (p + q + 1))).filter
      (· ≤ (⟨p, by omega⟩ : Fin (p + q + 1)))).card : ℤ)) :
    HEq ((ψ.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumLeftMap A B).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration e f)))).val.component
      ((Finset.univ : Finset (Fin (p + q + 1))).filter (· ≤ (⟨p, by omega⟩ : Fin (p + q + 1)))) k
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWIndex.left_nonempty (Finset.mem_univ (⟨p, by omega⟩ : Fin (p + q + 1)))) hk)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlagEvaluation e ψ) := by
  have hp : k = -(p : ℤ) := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubePrefixOrder_card] at hk; omega
  subst hp
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval_pullback_injective (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubePrefixOrder p q)
    (ψ.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumLeftMap A B).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration e f))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubePrefixOrder_injective p q)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubePrefixOrder_image_univ] at ht
  apply heq_of_eq
  refine ht.symm.trans ?_
  refine (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) y z p)
    (ψ.naturality_apply (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubePrefixOrder p q)).op
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumLeftMap A B).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration e f)))).symm).trans ?_
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumLeftMap_flag_prefix]
  rfl

/-- 概要：連結した旗の右射影の接尾成分は元の右の旗の最上位評価である。
方針：接尾包含の像に沿う成分計算と単体集合の射の自然性を使う。
規約：次数 k を濃度で指定し、−q との同定を異種等号で表す。
使われ方：HA 1.3.1.16 の AW の前の射の成分の計算。 -/
lemma standardComponent_cubeSum_suffix {A B : Type u} {p q : ℕ}
    (e : Fin p ≃ A) (f : Fin q ≃ B)
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) (k : ℤ)
    (hk : k = 1 - (((Finset.univ : Finset (Fin (p + q + 1))).filter
      ((⟨p, by omega⟩ : Fin (p + q + 1)) ≤ ·)).card : ℤ)) :
    HEq ((φ.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumRightMap A B).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration e f)))).val.component
      ((Finset.univ : Finset (Fin (p + q + 1))).filter ((⟨p, by omega⟩ : Fin (p + q + 1)) ≤ ·)) k
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWIndex.right_nonempty (Finset.mem_univ (⟨p, by omega⟩ : Fin (p + q + 1)))) hk)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlagEvaluation f φ) := by
  have hp : k = -(q : ℤ) := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSuffixOrder_card] at hk; omega
  subst hp
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval_pullback_injective (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSuffixOrder p q)
    (φ.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumRightMap A B).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration e f))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSuffixOrder_injective p q)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSuffixOrder_image_univ] at ht
  apply heq_of_eq
  refine ht.symm.trans ?_
  refine (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) x y q)
    (φ.naturality_apply (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSuffixOrder p q)).op
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumRightMap A B).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration e f)))).symm).trans ?_
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumRightMap_flag_suffix]
  rfl

/-- 概要：境目の AW 項は元の二つの旗の最上位評価の dg 合成である。
方針：両成分の異種等号と次数の濃度計算を通常順合成へ移す。
規約：任意の p,q を扱い、どちらかが零の場合も含む。
使われ方：Kerodon 2.5.8（Tag 00S0） の AW∘shuffle の唯一の非零項の評価。 -/
lemma awTerm_cubeSum_eq_comp {A B : Type u} {p q : ℕ}
    (e : Fin p ≃ A) (f : Fin q ≃ B)
    (ψ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) y z)
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm (ψ.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumLeftMap A B).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration e f)))).val
      (φ.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumRightMap A B).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration e f)))).val
      Finset.univ ⟨(⟨p, by omega⟩ : Fin (p + q + 1)), Finset.mem_univ _⟩
      (-((p + q : ℕ) : ℤ)) (by simp) =
      compose R (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlagEvaluation e ψ) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlagEvaluation f φ) (by push_cast; omega) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWAssocTerms.compose_eq_of_heq
  · exact standardComponent_cubeSum_prefix e f ψ _ _
  · exact standardComponent_cubeSum_suffix e f φ _ _
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSuffixOrder_card]
    push_cast
    omega
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubePrefixOrder_card]
    push_cast
    omega

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
