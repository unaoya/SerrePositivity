module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.PointReplacement
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingContraction
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
# 選んだ homotopy 重みの各値は可縮な Kan 複体

概要：Hovey §5 の射影 cofibrant な一点重みの各値に切断と収縮を構成する。
方針：境界の右類をすべての単射の右類へ移し、切断と区間の持ち上げを使う。
規約：切断と収縮は各頂点ごとのもの。図式全体での自然な切断は主張しない。
使われ方：homotopy 極限の重みの各値を一点と比較する。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomotopicalAlgebra
open scoped _root_.SSet.modelCategoryQuillen
open _root_.SerrePositivity.SimplicialModel.MonoRightLiftingContraction

variable (K : Type u) [SmallCategory K]

/-- 概要：重みの各値の比較はすべての単射に右持ち上げ性を持つ（Hovey §5）。
方針：境界の右類と単射の右類の一致を使う。
規約：元の単体集合の射そのものの性質。
使われ方：各値の Kan 性と実際の収縮。 -/
lemma comparison_mono_rlp (k : K) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.comparison K).app k) :=
  SSet.rlp_monomorphisms.ge _ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.comparison_rlp K k)

/-- 概要：選んだ重みの各値は Kan 複体（Hovey §5）。
方針：一点への射のホーンの右持ち上げ性を示す。
規約：単体集合のモデル構造の存在を使わない。
使われ方：一般 homotopy 極限の単体的重み。 -/
lemma weight_kanComplex (k : K) : SSet.KanComplex ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K).obj k) := by
  apply (isFibrant_iff_of_isTerminal ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.comparison K).app k) terminalIsTerminal).mpr
  apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
  exact MorphismProperty.antitone_rlp SSet.modelCategoryQuillen.J_le_monomorphisms _
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.comparison_mono_rlp K k)

/-- 概要：重みの各値の一点への射の切断（Hovey §5）。
方針：初期対象からの単射の持ち上げで選ぶ。
規約：この切断を添字圏に自然なものとは主張しない。
使われ方：各値の収縮の中心。 -/
def valueSection (k : K) : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.point K).obj k ⟶ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K).obj k :=
  Classical.choose (exists_section ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.comparison K).app k) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.comparison_mono_rlp K k))

/-- 概要：選んだ切断の一点への合成は恒等（Hovey §5）。
方針：切断を選んだ持ち上げの三角形を使う。
規約：各頂点の比較の同じ射を使う。
使われ方：重みの各値の明示的なホモトピー同値。 -/
lemma valueSection_comparison (k : K) :
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.valueSection K k ≫ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.comparison K).app k = 𝟙 _ :=
  Classical.choose_spec (exists_section ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.comparison K).app k) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.comparison_mono_rlp K k))

/-- 概要：重みの各値の恒等射を選んだ一点へ収縮する（Hovey §5）。
方針：区間境界の単射に沿う持ち上げを選ぶ。
規約：実際の単体的ホモトピーであり、時間の両端は指定した射。
使われ方：各値の可縮性の具体的な証明。 -/
def valueContraction (k : K) :
    SSet.Homotopy (𝟙 ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K).obj k)) ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.comparison K).app k ≫ _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.valueSection K k) :=
  Classical.choose (exists_vertical_contraction ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.comparison K).app k)
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.comparison_mono_rlp K k) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.valueSection K k) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.valueSection_comparison K k))

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
