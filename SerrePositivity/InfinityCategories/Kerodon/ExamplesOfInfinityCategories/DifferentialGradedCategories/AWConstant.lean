module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWBilinear

/-!
# 標準 Hom の定数単体

概要：閉次数零射を全ての次数の定数単体にし、一点成分と高次成分の値を計算する。
方針：標準零単体を唯一の写像 [n]→[0] に沿って引き戻す。
規約：定数単体は全ての一点成分に閉零射を持ち、高次成分は零。
使われ方：HA 1.3.1.13、Kerodon 2.5.8（Tag 00S0） の AW の単位則。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y : D}

/-- 概要：閉次数零射から任意の次数の標準の定数単体を作る。
方針：標準零単体を定数の単調写像に沿って引き戻す。
規約：標準方程式の保存は既存の引き戻しにより保証される。
使われ方：HA 1.3.1.13 の単体的 Hom の単位。 -/
def standardConstant (z : _root_.SerrePositivity.DifferentialGraded.zeroCycles (_root_.SerrePositivity.DifferentialGraded.homObject R D x y)) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y n :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback (OrderHom.const (Fin (n + 1)) (0 : Fin 1)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroLift z)

/-- 概要：定数単体の一点集合の成分は指定した閉零射である。
方針：一点集合上の単射性で引き戻しを計算し、零単体の成分を評価する。
規約：cochain 次数は零。
使われ方：Kerodon 2.5.8（Tag 00S0） の AW の単位項の回収。 -/
lemma standardConstant_singleton (z : _root_.SerrePositivity.DifferentialGraded.zeroCycles (_root_.SerrePositivity.DifferentialGraded.homObject R D x y)) {n : ℕ}
    (j : Fin (n + 1)) :
    (standardConstant z n).val.component {j} 0 (Finset.singleton_nonempty j) (by simp) = z.val := by
  rw [standardConstant, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback_val,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _ (by simp)]
  simp only [Finset.image_singleton]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.singleComponent (n := 0) Finset.univ 0 Finset.univ_nonempty (by simp) z.val).component
    Finset.univ 0 Finset.univ_nonempty (by simp) = z.val
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.singleComponent_self _ _ _ _ z.val

/-- 概要：定数単体の二点以上の成分は零である。
方針：定数写像は二点以上の集合上で単射でないことを使う。
規約：次数はその集合の標準次数。
使われ方：Kerodon 2.5.8（Tag 00S0） の AW の非単位項の消滅。 -/
lemma standardConstant_component_zero (z : _root_.SerrePositivity.DifferentialGraded.zeroCycles (_root_.SerrePositivity.DifferentialGraded.homObject R D x y)) {n : ℕ}
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hcard : 2 ≤ J.card) : (standardConstant z n).val.component J k hJ hk = 0 := by
  rw [standardConstant, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback_val]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_not_inj
  intro hi
  have hc := Finset.card_image_of_injOn hi
  have he : J.image (OrderHom.const (Fin (n + 1)) (0 : Fin 1)) = {0} := by
    ext a
    simp only [Finset.mem_image, Finset.mem_singleton]
    change (∃ j ∈ J, (0 : Fin 1) = a) ↔ a = 0
    exact ⟨fun ⟨_, _, ha⟩ ↦ ha.symm, fun ha ↦ ⟨hJ.choose, hJ.choose_spec, ha.symm⟩⟩
  rw [he, Finset.card_singleton] at hc
  omega

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
