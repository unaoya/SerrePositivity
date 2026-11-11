module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoordinateSigns
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedLinearReindex

/-!
# N4 成分族と標準 chain map 成分族の比較

概要：次数符号による成分族の変換は標準の削除境界と整合し、全ての引き戻しと可換である。
方針：点の前後の数による符号の比較を各削除項に適用する。
規約：空でない集合の次数は従来どおり 1−|J|。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ） の標準 DK 単体の構成。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y : D}

/-- 概要：各成分に次数符号を掛ける線形写像を定義する。
方針：有限集合の濃度から chain 次数を取り、整数として作用させる。
規約：係数環 R の作用と整数の作用を区別する。
使われ方：HA 1.3.1.12 の N4 成分から標準 chain map 成分への変換。 -/
def signChangeData {n : ℕ} : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n →ₗ[R] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n where
  toFun f i := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign (i.val.1.card - 1) • f i
  map_add' f g := by funext i; exact smul_add _ _ _
  map_smul' a f := by funext i; exact smul_comm _ _ _

/-- 概要：符号変換の指定された有限集合の成分は元の成分への符号の作用である。
方針：成分と線形写像の定義を評価する。
規約：次数とその等式の証明を引数として保持する。
使われ方：HA 1.3.1.12 の全成分の計算。 -/
lemma signChangeData_component {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (signChangeData f).component J k hJ hk =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign (J.card - 1) • f.component J k hJ hk := rfl

/-- 概要：成分族の符号変換は自分自身を逆写像に持つ。
方針：各成分で整数符号の二重作用を消す。
規約：全ての成分族に成立し、方程式を仮定しない。
使われ方：HA 1.3.1.12 の標準座標との両逆則。 -/
lemma signChangeData_involutive {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n) :
    signChangeData (signChangeData f) = f := by
  funext i
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign_smul_involutive _ _

/-- 概要：標準単体の境界の順序符号による削除和を定義する。
方針：削除点より小さい点の個数で係数を取る。
規約：一点集合では零として閉零元の条件に対応させる。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ） の正規化標準単体からの chain map 方程式。 -/
def standardRhs {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n) (J : Finset (Fin (n + 1)))
    (k : ℤ) (hk : k = 1 - (J.card : ℤ)) : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y (k + 1) :=
  if hJ : 2 ≤ J.card then
    ∑ j : J, (-1 : ℤ) ^ (J.filter (· < j.val)).card •
      f.component (J.erase j.val) (k + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty hJ j.val j.property)
        (by have := Finset.card_erase_add_one j.property; omega)
  else 0

/-- 概要：符号変換した成分の標準削除和は元の N4 の削除和の符号倍である。
方針：各削除項に次数符号と境界符号の恒等式を適用する。
規約：小さい集合でも両削除和は零となる。
使われ方：HA 1.3.1.12 の標準方程式と N4 方程式の同値。 -/
lemma standardRhs_signChangeData {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    standardRhs (signChangeData f) J k hk = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign (J.card - 1) • f.rhs J k hk := by
  unfold standardRhs _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.rhs
  split_ifs with hJ
  · rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [signChangeData_component]
    simp only [Units.smul_def, ← mul_smul]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign_deletion J j.val hJ j.property]
  · exact (smul_zero _).symm

/-- 概要：成分族の符号変換は全ての単調写像による引き戻しと可換である。
方針：単射な集合では濃度が保たれ、潰れる集合では両辺が零になる。
規約：面と退化の両方を含む。
使われ方：HA 1.3.1.12 の DK 単体の比較の単体的自然性。 -/
lemma signChangeData_pullback {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n) :
    signChangeData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α f) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α (signChangeData f) := by
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (signChangeData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α f)).component J k hJ hk =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α (signChangeData f)).component J k hJ hk
  rw [signChangeData_component]
  by_cases hi : Set.InjOn α (J : Set (Fin (m + 1)))
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj α f J k hJ hk hi,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj α (signChangeData f) J k hJ hk hi,
      signChangeData_component]
    congr 1
    rw [Finset.card_image_of_injOn hi]
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_not_inj α f J k hJ hk hi,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_not_inj α (signChangeData f) J k hJ hk hi,
      smul_zero]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
