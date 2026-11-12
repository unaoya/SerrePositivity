module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeSumFlags
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWDegenerate

/-!
# 和の座標の逆転と AW 評価の消滅

概要：左射影が忘れる右座標の後に右射影が忘れる左座標が現れる旗の AW 評価は零である。
方針：隣接する頂点の重複を見つけ、各切断点の接頭または接尾の成分を零にする。
規約：左の和の座標が後の射、右の和の座標が前の射。
使われ方：HA 1.3.1.16、Kerodon 2.5.8（Tag 00S0） の全置換のうち不適合な旗の消去。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial

/-- 概要：左射影の旗は右座標が加わる前後で同じ頂点を持つ。
方針：左座標の逆番号はその右座標の番号と異なる。
規約：元の番号付けの順序は任意。
使われ方：Kerodon 2.5.8（Tag 00S0） の左射影の接頭成分の退化の検出。 -/
lemma cubeSumLeftMap_flag_repeat {A B : Type u} {m : ℕ} (e : Fin m ≃ A ⊕ B)
    (r : Fin m) (b : B) (hr : e r = Sum.inr b) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumLeftMap A B).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e)).obj r.castSucc =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumLeftMap A B).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e)).obj r.succ := by
  apply Set.ext
  intro a
  change (e.symm (Sum.inl a)).val < r.val ↔ (e.symm (Sum.inl a)).val < r.val + 1
  have hne : (e.symm (Sum.inl a)).val ≠ r.val := by
    intro h
    have he := congrArg e (Fin.ext h)
    rw [e.apply_symm_apply, hr] at he
    cases he
  omega

/-- 概要：右射影の旗は左座標が加わる前後で同じ頂点を持つ。
方針：右座標の逆番号はその左座標の番号と異なる。
規約：元の番号付けの順序は任意。
使われ方：Kerodon 2.5.8（Tag 00S0） の右射影の接尾成分の退化の検出。 -/
lemma cubeSumRightMap_flag_repeat {A B : Type u} {m : ℕ} (e : Fin m ≃ A ⊕ B)
    (s : Fin m) (a : A) (hs : e s = Sum.inl a) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumRightMap A B).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e)).obj s.castSucc =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumRightMap A B).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e)).obj s.succ := by
  apply Set.ext
  intro b
  change (e.symm (Sum.inr b)).val < s.val ↔ (e.symm (Sum.inr b)).val < s.val + 1
  have hne : (e.symm (Sum.inr b)).val ≠ s.val := by
    intro h
    have he := congrArg e (Fin.ext h)
    rw [e.apply_symm_apply, hs] at he
    cases he
  omega

variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y z : D}

/-- 概要：右座標が左座標より先に現れる旗の各 AW 項は零である。
方針：切断点が逆転の前の座標より後なら接頭、それ以外なら接尾の頂点が重複する。
規約：座標を具体的に a,b として指定する。
使われ方：HA 1.3.1.16 の不適合な置換の旗の消去。 -/
lemma awTerm_cubeSum_zero_of_inversion {A B : Type u} {m : ℕ}
    (e : Fin m ≃ A ⊕ B) (r s : Fin m) (hrs : r < s)
    (a : A) (b : B) (hr : e r = Sum.inr b) (hs : e s = Sum.inl a)
    (ψ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) y z)
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y)
    (j : Fin (m + 1)) (k : ℤ)
    (hk : k = 1 - ((Finset.univ : Finset (Fin (m + 1))).card : ℤ)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm (ψ.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumLeftMap A B).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e))).val
      (φ.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumRightMap A B).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e))).val
      Finset.univ ⟨j, Finset.mem_univ j⟩ k hk = 0 := by
  by_cases hj : r.val < j.val
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm_nerve_zero_left
    intro hinj
    have h₀ : r.castSucc ∈ (Finset.univ : Finset (Fin (m + 1))).filter (· ≤ j) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change r.val ≤ j.val; omega⟩
    have h₁ : r.succ ∈ (Finset.univ : Finset (Fin (m + 1))).filter (· ≤ j) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change r.val + 1 ≤ j.val; omega⟩
    exact (ne_of_lt r.castSucc_lt_succ) (hinj h₀ h₁ (cubeSumLeftMap_flag_repeat e r b hr))
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm_nerve_zero_right
    intro hinj
    have h₀ : s.castSucc ∈ (Finset.univ : Finset (Fin (m + 1))).filter (j ≤ ·) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        change j.val ≤ s.val
        have h : r.val < s.val := hrs
        omega⟩
    have h₁ : s.succ ∈ (Finset.univ : Finset (Fin (m + 1))).filter (j ≤ ·) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        change j.val ≤ s.val + 1
        have h : r.val < s.val := hrs
        omega⟩
    exact (ne_of_lt s.castSucc_lt_succ) (hinj h₀ h₁ (cubeSumRightMap_flag_repeat e s a hs))

/-- 概要：右座標が左座標より先に現れる旗の AW の最上位評価は零である。
方針：切断点ごとの零の式を全切断点で足す。
規約：任意の次元 m で述べ、逆転が存在することを前提にする。
使われ方：Kerodon 2.5.8（Tag 00S0） の全置換の和を区間内置換の和へ制限する。 -/
lemma standardTopEval_AW_cubeSum_zero_of_inversion {A B : Type u} {m : ℕ}
    (e : Fin m ≃ A ⊕ B) (r s : Fin m) (hrs : r < s)
    (a : A) (b : B) (hr : e r = Sum.inr b) (hs : e s = Sum.inl a)
    (ψ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) y z)
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) x z m
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW (ψ.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumLeftMap A B).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e)))
        (φ.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumRightMap A B).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e)))) = 0 := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData (n := m) _ _).component Finset.univ (-(m : ℤ))
    Finset.univ_nonempty (by simp) = 0
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_component]
  apply Finset.sum_eq_zero
  intro j _
  exact awTerm_cubeSum_zero_of_inversion e r s hrs a b hr hs ψ φ j.val _ _

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
