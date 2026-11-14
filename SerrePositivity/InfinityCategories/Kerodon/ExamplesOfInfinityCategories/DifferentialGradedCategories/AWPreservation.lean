module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWBoundaryReindex

/-!
# AW 合成の標準方程式の保存

概要：標準単体の AW 成分族は再び標準単体の方程式を満たす。
方針：微分を左右の削除和へ展開し、添字の同値で非対角項と対角項へ分けて相殺する。
規約：合成の閉性は結論として証明し、追加の豊穣合成の仮定にしない。
使われ方：HA 1.3.1.13、Kerodon 2.5.8（Tag 00S0） の C_Δ の豊穣合成の構成。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y z : D}

/-- 概要：AW 成分族の全域評価は空集合も含めて切断項の和である。
方針：非空集合では通常の評価に戻し、空集合では両辺を零とする。
規約：集合の濃度に対応する次数を指定する。
使われ方：Kerodon 2.5.8（Tag 00S0） の削除後の AW の和を標準境界へ戻す。 -/
lemma awData_componentOrZero {n : ℕ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData g f).componentOrZero J k = ∑ i : J, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm g f J i k hk := by
  by_cases hJ : J.Nonempty
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.componentOrZero_eq _ _ _ hJ hk, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_component]
  · have he : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    subst J
    simp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.componentOrZero_empty]

/-- 概要：標準単体の AW 合成の各成分の微分は標準境界に等しい。
方針：左右の削除和を添字の同値で移し、非対角を削除後の AW 項へ、対角を零へ同定する。
規約：非空集合の全ての成分に成立する。
使われ方：HA 1.3.1.13 の標準単体の方程式の保存。 -/
lemma differential_awData_eq_standardRhs {n : ℕ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R y z n)
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y n) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    differential R ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData g.val f.val).component J k hJ hk) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardRhs (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData g.val f.val) J k hk := by
  let A := (Σ i : J, ↥(J.filter (· ≤ i.val))) ⊕ (Σ i : J, ↥(J.filter (i.val ≤ ·)))
  let B := (Σ j : J, ↥(J.erase j.val)) ⊕ (J ⊕ J)
  let X : A → _root_.SerrePositivity.DifferentialGraded.GradedHom R x z (k + 1) := fun a ↦ match a with
    | .inl p => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryLeftTerm g.val f.val J p.1 p.2.val k hk
    | .inr p => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryRightTerm g.val f.val J p.1 p.2.val k hk
  let Y : B → _root_.SerrePositivity.DifferentialGraded.GradedHom R x z (k + 1) := fun b ↦ match b with
    | .inl p => (-1 : ℤ) ^ (J.filter (· < p.1.val)).card •
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm g.val f.val (J.erase p.1.val) p.2 (k + 1)
          (by have := Finset.card_erase_add_one p.1.property; omega)
    | .inr (.inl i) => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryLeftTerm g.val f.val J i i.val k hk
    | .inr (.inr i) => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryRightTerm g.val f.val J i i.val k hk
  have hs : (∑ a : A, X a) = ∑ b : B, Y b := by
    apply Fintype.sum_equiv (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.boundaryPairEquiv J)
    intro a
    rcases a with ⟨i, j⟩ | ⟨i, j⟩
    · change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryLeftTerm g.val f.val J i j.val k hk =
        Y (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.boundaryPairMap J (.inl ⟨i, j⟩))
      dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.boundaryPairMap]
      split_ifs with he
      · exact congrArg (fun t ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryLeftTerm g.val f.val J i t k hk) he
      · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryLeftTerm_of_lt g.val f.val J i j.val
          (Finset.mem_filter.mp j.property).1
          (lt_of_le_of_ne (Finset.mem_filter.mp j.property).2 he) k hk
    · change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryRightTerm g.val f.val J i j.val k hk =
        Y (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.boundaryPairMap J (.inr ⟨i, j⟩))
      dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.boundaryPairMap]
      split_ifs with he
      · exact congrArg (fun t ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryRightTerm g.val f.val J i t k hk) he
      · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryRightTerm_of_lt g.val f.val J i j.val
          (Finset.mem_filter.mp j.property).1
          (lt_of_le_of_ne (Finset.mem_filter.mp j.property).2 (Ne.symm he)) k hk
  simp only [A, B, X, Y, Fintype.sum_sum_type, Fintype.sum_sigma] at hs
  have hd : (∑ i : J, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryLeftTerm g.val f.val J i i.val k hk) +
      ∑ i : J, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryRightTerm g.val f.val J i i.val k hk = 0 := by
    simp_rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryLeftTerm_diag, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryRightTerm_diag]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awDiagonal_sum_eq_zero g.val f.val J (k + 1)
  rw [hd, add_zero] at hs
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.differential_awData_component_eq_sums, hs, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardRhs_eq_deleteSum]
  apply Finset.sum_congr rfl
  intro j _
  rw [awData_componentOrZero _ _ _ _ (by have := Finset.card_erase_add_one j.property; omega),
    Finset.smul_sum]

/-- 概要：標準単体の AW 成分族は標準単体の部分加群に属する。
方針：各非空集合で微分と標準境界の等式を適用する。
規約：任意の dg 圏と全ての次数で追加仮定なく成立する。
使われ方：HA 1.3.1.13 の単体的豊穣合成の閉性。 -/
lemma awData_mem_standard {n : ℕ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R y z n)
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y n) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData g.val f.val ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSubmodule R x z n := by
  intro J k hJ hk
  exact differential_awData_eq_standardRhs g f J k hJ hk

/-- 概要：標準単体の Alexander–Whitney 合成を定義する。
方針：成分族の AW 演算に標準方程式の保存の証明を添える。
規約：通常順に後の射 g、前の射 f を引数に取る。
使われ方：HA 1.3.1.13、Kerodon 2.5.8（Tag 00S0） の C_Δ の合成。 -/
def standardAW {n : ℕ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R y z n) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x z n := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData g.val f.val, awData_mem_standard g f⟩

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.3.1.13" (partial := component) "仮定：dg 圏 C（HA の CΔ の構成と一致。Lean は任意の可換環を許す）。結論：基礎圏を単体的に豊穣化し、Hom を切断した Hom 複体の Dold–Kan 模型と比較し、合成を Alexander–Whitney 写像で与える。任意の鎖複体に対する合成関手そのものの lax monoidal 構造は型に含まれない（Lean が弱い）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW
