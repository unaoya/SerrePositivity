module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NormalizedSupport

/-!
# 正規化された標準単体の最上位成分による検出

概要：正規化された正次数の標準単体は全体集合の成分だけで決まる。
方針：標準方程式で零番目の面を最上位成分の微分に同定し、他の成分は支持の消滅を使う。
規約：逆写像の構成や Mathlib の正規化との同型は別途必要である。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ） の正規化 Hom 複体の比較の単射性。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y : D}

/-- 概要：正規化された標準単体の全体集合の削除和には零番目の面だけが残る。
方針：有限和の零番目の項を取り出し、正の頂点を欠く他の成分を消す。
規約：全体集合の成分の次数を証明引数として保持する。
使われ方：HA 1.3.1.12 の正規化微分 d₀ の計算。 -/
lemma standardRhs_normalized_univ {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y (n + 1))
    (hf : f ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizedSubmodule R x y (n + 1)) (k : ℤ)
    (hk : k = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardRhs f.val Finset.univ k hk =
      f.val.component (Finset.univ.erase 0) (k + 1)
        (by apply Finset.card_pos.mp; simp)
        (by simp at hk ⊢; omega) := by
  have hu : 2 ≤ (Finset.univ : Finset (Fin (n + 2))).card := by simp
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardRhs, dite_eq_left hu]
  rw [Finset.sum_eq_single (⟨0, Finset.mem_univ _⟩ :
    (Finset.univ : Finset (Fin (n + 2))))]
  · have hfilter : (Finset.univ : Finset (Fin (n + 2))).filter (· < 0) = ∅ := by
      ext j
      simp
    rw [hfilter, Finset.card_empty, pow_zero, one_smul]
  · intro j _ hj
    have hj0 : j.val ≠ 0 := fun he ↦ hj (Subtype.ext he)
    obtain ⟨t, ht⟩ := Fin.exists_succ_eq_of_ne_zero hj0
    have hz := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalized_component_zero_of_notMem f hf t (Finset.univ.erase j.val)
      (by rw [ht]; simp) (k + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty hu j.val j.property)
      (by have hc := Finset.card_erase_add_one j.property; omega)
    rw [hz, smul_zero]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- 概要：正規化された単体の零番目の面の成分は最上位成分の微分である。
方針：標準方程式と正規化後の削除和の計算を合成する。
規約：正規化の符号は Mathlib と同じ d₀。
使われ方：HA 1.3.1.12 の切断 Hom の微分との比較。 -/
lemma normalized_top_differential {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y (n + 1))
    (hf : f ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizedSubmodule R x y (n + 1)) (k : ℤ)
    (hk : k = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ)) :
    _root_.SerrePositivity.DifferentialGraded.differential R (f.val.component Finset.univ k Finset.univ_nonempty hk) =
      f.val.component (Finset.univ.erase 0) (k + 1)
        (by apply Finset.card_pos.mp; simp)
        (by simp at hk ⊢; omega) :=
  (f.property Finset.univ k Finset.univ_nonempty hk).trans
    (standardRhs_normalized_univ f hf k hk)

/-- 概要：正規化された正次数の単体を全体集合の成分で評価する線形写像。
方針：濃度 n+2 の集合の cochain 次数 −(n+1) の成分を取る。
規約：値は切断 Hom 複体の正次数の項と同じ次数。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ） の正規化複体の比較写像。 -/
def normalizedTopEval (x y : D) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizedSubmodule R x y (n + 1) →ₗ[R] GradedHom R x y (-(n + 1 : ℤ)) where
  toFun f := f.val.val.component Finset.univ (-(n + 1 : ℤ)) Finset.univ_nonempty
    (by simp)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 概要：正規化された正次数の単体は最上位成分により一意に決まる。
方針：全体集合で仮定を使い、零番目の面では微分を取り、他の集合では消滅を使う。
規約：正規化条件からの帰結であり、追加の支持の仮定は要求しない。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ） の正規化の同型の単射性。 -/
lemma normalizedTopEval_injective (x y : D) (n : ℕ) :
    Function.Injective (normalizedTopEval (R := R) x y n) := by
  intro f g h
  apply Subtype.ext
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change f.val.val.component J k hJ hk = g.val.val.component J k hJ hk
  by_cases hfull : J = Finset.univ
  · subst J
    have hkk : k = -(n + 1 : ℤ) := by
      simp at hk
      omega
    subst k
    exact h
  by_cases hface : J = Finset.univ.erase 0
  · subst J
    have hc : (Finset.univ.erase (0 : Fin (n + 2))).card = n + 1 := by simp
    have hkk : k = -(n + 1 : ℤ) + 1 := by
      rw [hc] at hk
      push_cast at hk
      omega
    subst k
    have hd := congrArg (_root_.SerrePositivity.DifferentialGraded.differential R) h
    exact (normalized_top_differential f.val f.property (-(n + 1 : ℤ)) (by simp; omega)).symm.trans
      (hd.trans (normalized_top_differential g.val g.property (-(n + 1 : ℤ)) (by simp; omega)))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalized_component_zero f.val f.property J k hJ hk hfull hface).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalized_component_zero g.val g.property J k hJ hk hfull hface).symm

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
