module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.Generators

/-!
# 添字圏の同値に沿う重みの射影 cofibration

概要：Hovey §5 の射影境界の左類は添字圏の同値による前合成で保たれる。
方針：関手圏の同値の随伴で持ち上げを移し、右類を各頂点で判定する。
規約：通常の添字圏の同値を使い、単体集合のモデル構造は不要。
使われ方：二重反対圏へ移した cofibrant 重みを元の小圏の end に入力する。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight

open _root_.CategoryTheory

variable {J K : Type u} [SmallCategory J] [SmallCategory K]

/-- 概要：添字の同値に沿う前合成は射影境界の左類を保つ（Hovey §5）。
方針：関手圏の同値の随伴と評価の右類判定を使う。
規約：同値以外の制限関手への保存は仮定しない。
使われ方：重みの二重反対化と右 frame の添字を合わせる。 -/
lemma reindex_cofibration (e : J ≌ K) {W W' : K ⥤ SSet.{u}} (i : W ⟶ W')
    (hi : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries K).rlp.llp i) :
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries J).rlp.llp
      (((Functor.whiskeringLeft J K SSet.{u}).obj e.functor).map i) := by
  intro X Y p hp
  apply ((e.symm.congrLeft.toAdjunction).hasLiftingProperty_iff i p).mpr
  apply hi
  apply (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries_rlp K).ge
  intro k
  exact (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries_rlp J).le _ hp (e.inverse.obj k)

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
