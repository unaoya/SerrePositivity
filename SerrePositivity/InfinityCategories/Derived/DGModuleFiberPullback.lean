module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberBoundaryJoinFaces

/-! # 標準 fiber の錐は ∞ 引き戻し

概要：dg 加群の標準 fiber の錐は dg nerve の cospan の極限錐である。
方針：slice の任意の正次元境界を二セルの有限成分で直接充填し、curry して終対象性を得る。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：β3 の dg 加群の標準引き戻し。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories

open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 概要：標準 fiber の錐は dg 加群の dg nerve の cospan の極限錐である。
方針：最後の頂点が標準錐である slice 境界に明示的な左右の単体を作り、貼合せた join 写像を curry する。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：標準 fiber 四角形の ∞ 引き戻し性。 -/
lemma dgModuleFiberCone_isLimit (f : M ⟶ N) :
    IsLimitCone (dgModuleFiberCone A D f) := by
  intro n b hb
  let F := dgModuleFiberBoundaryJoinFiller A D f b hb
  have hfaces := dgModuleFiberBoundaryJoinFiller_faces A D f b hb
  refine ⟨sliceOverCurry F (joinBoundaryFaces_fixed _ b F hfaces), ?_⟩
  exact sliceOverCurry_boundary_of_joinFaces _ b F hfaces

/-- 概要：標準 mapping cone の −1 シフトによる fiber 四角形は dg nerve の ∞ 引き戻し四角形である。
方針：対応する標準錐の slice の終対象性を引き戻し四角形の定義へ戻す。
規約：HTT §1.2.13、HA §1.3.1。使われ方：錐で閉じた充満 dg 部分圏と擬同型判定への入力。 -/
lemma dgModuleFiberSquare_isPullback (f : M ⟶ N) :
    IsPullbackSquare (dgModuleFiberSquare A D f) :=
  dgModuleFiberCone_isLimit A D f

end SerrePositivity.InfinityCategories
