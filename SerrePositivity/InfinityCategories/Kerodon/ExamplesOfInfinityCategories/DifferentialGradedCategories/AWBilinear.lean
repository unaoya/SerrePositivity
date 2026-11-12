module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWData

/-!
# Alexander–Whitney 合成の双線形性

概要：AW 成分族の演算は各変数について R 線形である。
方針：通常順の斉次合成の R 双線形性を各切断点に適用し和を取る。
規約：方程式を課す前の成分族の加群上で述べる。
使われ方：HA 1.3.1.13、Kerodon 2.5.8（Tag 00S0） の単体的豊穣合成の線形構造。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y z : D}

/-- 概要：通常順の斉次合成は後の射の R スカラー倍を保つ。
方針：tensor の第二変数の線形性と整数符号の作用との可換性を使う。
規約：次数の和を証明引数で指定する。
使われ方：Kerodon 2.5.8（Tag 00S0） の AW の後の射についての線形性。 -/
lemma compose_smul_left {p q k : ℤ} (a : R) (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R y z q)
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y p) (hk : p + q = k) :
    _root_.SerrePositivity.DifferentialGraded.compose R (a • g) f hk = a • compose R g f hk := by
  unfold _root_.SerrePositivity.DifferentialGraded.compose _root_.SerrePositivity.DifferentialGraded.forward
  rw [TensorProduct.tmul_smul, map_smul, map_smul]
  exact smul_comm _ _ _

/-- 概要：通常順の斉次合成は前の射の R スカラー倍を保つ。
方針：tensor の第一変数の線形性と整数符号の作用との可換性を使う。
規約：次数の和を証明引数で指定する。
使われ方：Kerodon 2.5.8（Tag 00S0） の AW の前の射についての線形性。 -/
lemma compose_smul_right {p q k : ℤ} (a : R) (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R y z q)
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y p) (hk : p + q = k) :
    _root_.SerrePositivity.DifferentialGraded.compose R g (a • f) hk = a • compose R g f hk := by
  unfold _root_.SerrePositivity.DifferentialGraded.compose _root_.SerrePositivity.DifferentialGraded.forward
  rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul, map_smul]
  exact smul_comm _ _ _

/-- 概要：AW 合成は後の射の成分族の R スカラー倍を保つ。
方針：各切断点の合成からスカラーを外へ出す。
規約：任意の成分族に成立する。
使われ方：Kerodon 2.5.8（Tag 00S0） の双線形写像の構成。 -/
lemma awData_smul_left {n : ℕ} (a : R) (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n)
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData (a • g) f = a • _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData g f := by
  funext i
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component, Pi.smul_apply, compose_smul_left,
    Finset.smul_sum]

/-- 概要：AW 合成は前の射の成分族の R スカラー倍を保つ。
方針：各切断点の合成からスカラーを外へ出す。
規約：任意の成分族に成立する。
使われ方：Kerodon 2.5.8（Tag 00S0） の双線形写像の構成。 -/
lemma awData_smul_right {n : ℕ} (a : R) (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n)
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData g (a • f) = a • _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData g f := by
  funext i
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component, Pi.smul_apply, compose_smul_right,
    Finset.smul_sum]

/-- 概要：標準成分族の AW 演算を R 双線形写像としてまとめる。
方針：各変数の加法性とスカラー倍の保存を使う。
規約：外側の変数が後の射 g、内側の変数が前の射 f。
使われ方：HA 1.3.1.13 の成分族から単体的加群の合成への制限。 -/
def awDataBilinear (x y z : D) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n →ₗ[R] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n →ₗ[R] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x z n where
  toFun g :=
    { toFun := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData g
      map_add' := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_add_right g
      map_smul' := fun a f ↦ awData_smul_right a g f }
  map_add' g g' := by
    apply LinearMap.ext
    intro f
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_add_left g g' f
  map_smul' a g := by
    apply LinearMap.ext
    intro f
    exact awData_smul_left a g f

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
