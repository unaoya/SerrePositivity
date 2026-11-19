module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SelfPullbackInverseEdge
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.ZeroMapComponents

/-!
概要：自己 pullback の交換と連結写像の逆元の成分の比較。
方針：逆元の三角形の持ち上げから得た辺を π₀ へ送る。
規約：全空間の収縮可能性をまだ使わない一般補題。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。二つの三角形の交換の符号。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra

noncomputable section

/-- 概要：逆元の三角形を持つ二つの連結射の代表は、自己 pullback の交換で同じ成分となる。
方針：構成した pullback 内の辺の両端点を π₀ へ送る。
規約：全空間の Kan 性は不要。
使われ方：Goerss–Jardine I §7。交換と逆元の幾何的な成分の等式。 -/
theorem selfPullback_inverse_components {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    (e : E _⦋0⦌) {s t : B.PtSimplex 1 (p.app _ e)}
    (Ls : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s) (Lt : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e t)
    (m : PtSimplex.MulStruct t s .const (0 : Fin 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.zeroMapComponent (Lt.boundary.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackFiberInclusion p e) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.zeroMapComponent (Ls.boundary.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackFiberInclusion p e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackSwap p) := by
  obtain ⟨r, h₁, h₀⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullback_exists_inverse_edge p e Ls Lt m
  rw [← h₁, ← h₀]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.zeroMapComponent_edge r

/-- 概要：任意の連結射の代表に対し、自己 pullback の交換は基本群の逆元の代表を与える。
方針：Kan 複体の逆元の三角形を選び、その持ち上げを成分で比較する。
規約：底 B の Kan 性と p の fibration 性だけを使う。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。収縮可能な全空間の場合の交換の逆元表示。 -/
theorem selfPullback_swap_inverse_representative {E B : SSet.{u}} (p : E ⟶ B)
    [Fibration p] [KanComplex B] (e : E _⦋0⦌)
    (s : B.PtSimplex 1 (p.app _ e)) (Ls : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s) :
    ∃ (t : B.PtSimplex 1 (p.app _ e)) (Lt : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e t),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk t = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s)⁻¹ ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.zeroMapComponent (Lt.boundary.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackFiberInclusion p e) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.zeroMapComponent
          (Ls.boundary.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackFiberInclusion p e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackSwap p) := by
  obtain ⟨t, ⟨m⟩⟩ := PtSimplex.MulStruct.exists_left_inverse s (0 : Fin 1)
  let Lt := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.chooseBoundaryLift p e t
  refine ⟨t, Lt, ?_, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullback_inverse_components p e Ls Lt m⟩
  exact eq_inv_of_mul_eq_one_left (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_eq m)

end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
