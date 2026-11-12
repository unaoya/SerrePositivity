module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardData
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomSpace

/-!
# 標準 chain map 方程式の線形単体

概要：標準単体の削除境界を満たす成分族を部分加群とし、N4 の線形解と線形同値にする。
方針：符号変換による二つの方程式の移送を両向きに証明する。
規約：次数零では閉元、正次数では通常の交代境界を課す。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ） の DK の具体的成分模型。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y : D}

/-- 概要：標準の chain map 方程式を満たす成分族は部分加群をなす。
方針：微分と通常の符号付き削除和がともに線形であることを使う。
規約：次数は 1−|J| の cochain 表示を保持する。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ） の標準 DK 単体。 -/
def standardSubmodule (R : Type u) [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
    (x y : D) (n : ℕ) : Submodule R (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n) where
  carrier := {f | ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)),
    differential R (f.component J k hJ hk) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardRhs f J k hk}
  zero_mem' := by
    intro J k hJ hk
    change (_root_.SerrePositivity.DifferentialGraded.homObject R D x y).d k (k + 1) 0 = _
    rw [map_zero]
    simp [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardRhs, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component]
  add_mem' := by
    intro f g hf hg J k hJ hk
    change (_root_.SerrePositivity.DifferentialGraded.homObject R D x y).d k (k + 1)
      (f.component J k hJ hk + g.component J k hJ hk) = _
    rw [map_add]
    change _root_.SerrePositivity.DifferentialGraded.differential R (f.component J k hJ hk) +
      _root_.SerrePositivity.DifferentialGraded.differential R (g.component J k hJ hk) = _
    rw [hf J k hJ hk, hg J k hJ hk]
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardRhs
    split_ifs
    · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component, Pi.add_apply, smul_add, Finset.sum_add_distrib]
    · simp
  smul_mem' := by
    intro a f hf J k hJ hk
    change (_root_.SerrePositivity.DifferentialGraded.homObject R D x y).d k (k + 1) (a • f.component J k hJ hk) = _
    rw [map_smul]
    change a • _root_.SerrePositivity.DifferentialGraded.differential R (f.component J k hJ hk) = _
    rw [hf J k hJ hk]
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardRhs
    split_ifs
    · rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact smul_comm _ _ _
    · exact smul_zero _

/-- 概要：標準 DK 単体の成分模型を標準方程式の解の型として定義する。
方針：標準方程式の部分加群の台型を使う。
規約：Mathlib の Γ と同じ定義だとはまだ仮定しない。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ） の標準単体からの chain map の成分。 -/
abbrev StandardSimplex (R : Type u) [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
    (x y : D) (n : ℕ) := ↥(standardSubmodule R x y n)

/-- 概要：N4 の線形解の符号変換は標準方程式を満たす。
方針：微分の整数線形性と標準削除和への符号変換の等式を使う。
規約：入力は実際の N4 の線形解。
使われ方：HA 1.3.1.12 の DK 成分への写像。 -/
lemma signChange_mem_standard {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x y n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.signChangeData f.val ∈ standardSubmodule R x y n := by
  intro J k hJ hk
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardRhs_signChangeData, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.signChangeData_component]
  change (_root_.SerrePositivity.DifferentialGraded.homObject R D x y).d k (k + 1)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign (J.card - 1) • f.val.component J k hJ hk) = _
  rw [map_zsmul]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign (J.card - 1) • differential R (f.val.component J k hJ hk) = _
  rw [f.property J k hJ hk]

/-- 概要：標準方程式の解の符号変換は N4 の線形方程式を満たす。
方針：標準削除和の変換を再度符号倍し、二重作用を消す。
規約：標準方程式だけを前提とする。
使われ方：HA 1.3.1.12 の N4 成分への逆写像。 -/
lemma signChange_mem_linear {n : ℕ} (f : StandardSimplex R x y n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.signChangeData f.val ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearSubmodule R x y n := by
  intro J k hJ hk
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.signChangeData_component]
  change (_root_.SerrePositivity.DifferentialGraded.homObject R D x y).d k (k + 1)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign (J.card - 1) • f.val.component J k hJ hk) = _
  rw [map_zsmul]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign (J.card - 1) • differential R (f.val.component J k hJ hk) = _
  rw [f.property J k hJ hk]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardRhs_signChangeData (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.signChangeData f.val) J k hk
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.signChangeData_involutive] at h
  have h' := congrArg (fun t ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign (J.card - 1) • t) h
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign_smul_involutive] using h'

/-- 概要：N4 の線形単体と標準 chain map 方程式の単体は R 線形同値である。
方針：両向きに同じ次数符号を掛け、二重変換が恒等となることを使う。
規約：全次数と任意の dg 圏の二対象を扱う。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ） の全次数の比較。 -/
def standardSimplexEquiv (x y : D) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x y n ≃ₗ[R] StandardSimplex R x y n where
  toFun f := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.signChangeData f.val, signChange_mem_standard f⟩
  invFun f := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.signChangeData f.val, signChange_mem_linear f⟩
  left_inv f := Subtype.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.signChangeData_involutive f.val)
  right_inv f := Subtype.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.signChangeData_involutive f.val)
  map_add' f g := Subtype.ext (map_add _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.signChangeData f.val g.val)
  map_smul' a f := Subtype.ext (map_smul _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.signChangeData a f.val)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
