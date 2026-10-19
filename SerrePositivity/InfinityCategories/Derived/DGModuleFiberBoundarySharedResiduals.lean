module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberBoundaryResiduals
public import SerrePositivity.InfinityCategories.DGNerve.CospanSharedRhs

/-! # 共通の型付き残差と右側データの比較

概要：先頭・D 側の右辺を一度だけ標準 Hom へ移し、右側の生の右辺とも異種等号で比較する。
方針：左側からの一つの線形移送に、共通面の異種等号を合成する。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：六成分の線形系で共通の r₀,r_D を使う。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories

open CategoryTheory Opposite DifferentialGraded DGNerve
open scoped Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 概要：一つに選んだ型付き先頭右辺は右の生の先頭右辺とも異種等号で一致する。
方針：左側からの移送と共通面の先頭右辺の比較を合成する。
規約：HTT §1.2.13。使われ方：右側の整合式にも同じ r₀ を使う。 -/
lemma dgModuleFiberBoundaryRhs0_heq_right {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) :
    HEq (dgModuleFiberBoundaryRhs0 A D f b hb) (dgModuleFiberBoundaryRightBase A D f
      b).cospanPrefixRhs := by
  unfold dgModuleFiberBoundaryRhs0
  apply gradedHomTransport_heq_of_heq (A := A) (D := RightModule A D)
  exact cospanBoundaryZeroData_prefixRhs_heq (A := A) (D := RightModule A D) (n := n)
    (sliceOverUncurry b)

/-- 概要：一つに選んだ型付き D 側右辺は右の生の D 側右辺とも異種等号で一致する。
方針：左側からの移送と共通面の D 側右辺の比較を合成する。
規約：HTT §1.2.13。使われ方：左右の三角形の整合式に同じ r_D を使う。 -/
lemma dgModuleFiberBoundaryRhsN_heq_right {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) :
    HEq (dgModuleFiberBoundaryRhsN A D f b hb) ((dgModuleFiberBoundaryRightBase A D f
      b).cospanOneTailRhs
      (cospanLastTail n) ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))) := by
  unfold dgModuleFiberBoundaryRhsN
  apply gradedHomTransport_heq_of_heq (A := A) (D := RightModule A D)
  exact cospanBoundaryZeroData_D_rhs_heq (A := A) (D := RightModule A D) (n := n)
    (sliceOverUncurry b)

/-- 概要：型付きの先頭の右辺は閉じている。
方針：元の境界データの閉性と Hom の移送による閉性の保存を使う。
規約：HA Proposition 1.3.1.10。使われ方：六成分の系の δr₀=0。 -/
lemma dgModuleFiberBoundaryRhs0_closed {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) :
    differential A (dgModuleFiberBoundaryRhs0 A D f b hb) = 0 := by
  change differential (D := RightModule A D) A (dgModuleFiberBoundaryRhs0 A D f b hb) = 0
  unfold dgModuleFiberBoundaryRhs0
  apply gradedHomTransport_closed (A := A) (D := RightModule A D)
  exact cospanBoundaryLeftZeroData_prefixRhs_closed (A := A) (D := RightModule A D) (n := n)
    (sliceOverUncurry b)

end SerrePositivity.InfinityCategories
