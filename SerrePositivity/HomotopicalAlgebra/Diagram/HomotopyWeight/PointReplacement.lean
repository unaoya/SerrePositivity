module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.Generators

/-!
# 定値一点重みの実際の射影 cofibrant 置換

概要：Hovey §5 の homotopy 極限に使う重みを境界の小対象分解から構成する。
方針：初期図式から定値一点への射を自由境界の左類と右類に分解する。
規約：任意の小圏、単体集合の完全なモデル構造を仮定しない。
使われ方：E 代数の右 frame の重み付き end に代入する標準重み。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable (K : Type u) [SmallCategory K]

/-- 概要：小圏上の定値一点重み（Hovey §5）。
方針：単体集合の終対象を全頂点に置く。
規約：空の添字圏も許す。
使われ方：homotopy 極限の重みの比較先。 -/
def point : K ⥤ SSet.{u} := (Functor.const K).obj (⊤_ SSet.{u})

/-- 概要：定値一点への自由境界の小対象分解（Hovey §2.1・§5）。
方針：証明済みの小対象性から実際の二段分解を選ぶ。
規約：左類と右類を明示し、重みの存在を仮定しない。
使われ方：重みとその cofibrancy・自明 Kan 比較を同時に構成する。 -/
def pointFactorization : MorphismProperty.MapFactorizationData
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries K).rlp.llp (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries K).rlp (initial.to (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.point K)) :=
  MorphismProperty.factorizationData _ _ _

/-- 概要：定値一点の射影 cofibrant 置換として選んだ重み（Hovey §5）。
方針：小対象分解の中間図式を取る。
規約：元の小圏上の実際の単体集合図式。
使われ方：E 代数図式の homotopy 極限を計算する重み。 -/
def weight : K ⥤ SSet.{u} := (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointFactorization K).Z

/-- 概要：選んだ重みから定値一点への比較（Hovey §5）。
方針：小対象分解の右射を使う。
規約：全図式射に厳密に自然。
使われ方：重みを通常の錐と比較する。 -/
def comparison : _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K ⟶ _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.point K := (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointFactorization K).p

/-- 概要：選んだ重みは自由境界で射影 cofibrant（Hovey §5）。
方針：小対象分解の左射を初期図式からの唯一の射と同定する。
規約：頂点ごとの cofibrancy への置き換えはしない。
使われ方：重み付き end の導来的な計算の左持ち上げ条件。 -/
lemma weight_cofibrant : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries K).rlp.llp (initial.to (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)) := by
  have he : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointFactorization K).i = initial.to (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) := initial.hom_ext _ _
  exact he ▸ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointFactorization K).hi

/-- 概要：比較の各値は実際の境界生成族に対して右持ち上げ性を持つ（Hovey §5）。
方針：小対象分解の右射を自由評価随伴で各頂点へ移す。
規約：単体集合のモデル構造を使わず自明 Kan の右類を直接指定する。
使われ方：各値の可縮性と Kan 性、重みの比較の構成。 -/
lemma comparison_rlp (k : K) : SSet.modelCategoryQuillen.I.rlp ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.comparison K).app k) := by
  exact (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries_rlp K).le _ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointFactorization K).hp k

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
