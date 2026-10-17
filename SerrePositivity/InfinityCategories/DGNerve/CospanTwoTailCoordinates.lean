module
public import SerrePositivity.InfinityCategories.DGNerve.CospanTwoTailResidual

/-! # 三角形側の右辺の固定次数での評価

概要：全体集合の右辺を零番目から最後の頂点への固定次数の射として読む。
方針：全体集合の端点と濃度 n+4 を用いる。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：r_BD・r_CD の Hom 座標への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：三角形側の右辺は零番目から最後への次数 −n−2+1 の射。
方針：全体集合の右辺に端点と次数を代入する。
規約：HA Proposition 1.3.1.10。使われ方：未知成分の線形系の三角形側の右辺。 -/
def cospanTwoTailRhs {n : ℕ} (s : SimplexData A D (n + 3)) :
    GradedHom A (s.obj 0) (s.obj (cospanLastTail n)) (-(n : ℤ) - 2 + 1) :=
  s.rhs Finset.univ 0 (cospanLastTail n) (-(n : ℤ) - 2)
    (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
    (HornData.univ_min_zero (n + 1) _) (HornData.univ_max_last (n + 1) _)
    (by simp only [Finset.card_univ, Fintype.card_fin]; push_cast; omega)

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
