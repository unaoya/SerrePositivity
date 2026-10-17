module
public import SerrePositivity.InfinityCategories.DGNerve.PinchedDataEquation

/-! # 線形解から右 pinched 単体への逆構成

概要：全線形方程式の解から実際の dg nerve の右 pinched 単体を構成する。
方針：再構成データの回収族が元の解であることから全単体方程式を導き、端点条件を添える。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：全次数の線形表示の逆写像。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex

open CategoryTheory DifferentialGraded
open scoped Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 概要：線形方程式の解から dg nerve の (n+1) 単体を構成する。
方針：再構成データが回収により元の解に戻ることから全単体方程式を証明する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：右 pinched 単体の逆構成の本体。 -/
def toSimplex {n : ℕ} (f : LinearSimplex A x y n) : Simplex A D (n + 1) where
  toSimplexData := f.val.toSimplexData
  equation I a b k hI ha hb hk := by
    have hr : Data.toLinearData f.val.toData ∈ linearSubmodule A x y n := by
      rw [LinearData.toLinearData_toData]
      exact f.property
    exact Data.equation_of_linear f.val.toData hr I a b k hI ha hb hk

/-- 概要：線形方程式の解から実際の右 pinched 単体を構成する。
方針：全単体方程式を持つ再構成単体に、先頭面と最終頂点の既証のデータの等式を添える。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：全次数の線形表示の逆写像。 -/
def toPinched {n : ℕ} (f : LinearSimplex A x y n) : (DGNerve.pinchedHom A D x y) _⦋n⦌ where
  val := f.toSimplex
  source := Simplex.ext f.val.toSimplexData_front
  target := Simplex.ext f.val.toSimplexData_last

/-- 概要：逆構成した右 pinched 単体を線形模型へ戻すと元の解になる。
方針：部分加群の外延性と再構成データの成分の片側の逆則を使う。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：全次数の同値の片側の逆。 -/
lemma toLinearSimplex_toPinched {n : ℕ} (f : LinearSimplex A x y n) :
    PinchedHom.toLinearSimplex f.toPinched = f := by
  apply Subtype.ext
  exact f.val.toSimplexData_toPinchedLinearData

end SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex
