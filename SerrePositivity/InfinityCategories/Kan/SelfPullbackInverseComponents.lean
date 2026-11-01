module

public import SerrePositivity.InfinityCategories.Kan.SelfPullbackInverseEdge
public import SerrePositivity.InfinityCategories.Kan.ZeroMapComponents

/-!
概要：自己 pullback の交換と連結写像の逆元の成分の比較。
方針：逆元の三角形の持ち上げから得た辺を π₀ へ送る。
規約：全空間の収縮可能性をまだ使わない一般補題。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5。二つの三角形の交換の符号。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

/-- 概要：逆元の三角形を持つ二つの連結射の代表は、自己 pullback の交換で同じ成分となる。
方針：構成した pullback 内の辺の両端点を π₀ へ送る。
規約：全空間の Kan 性は不要。
使われ方：Goerss–Jardine I §7。交換と逆元の幾何的な成分の等式。 -/
theorem selfPullback_inverse_components {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    (e : E _⦋0⦌) {s t : B.PtSimplex 1 (p.app _ e)}
    (Ls : BoundaryLift p e s) (Lt : BoundaryLift p e t)
    (m : PtSimplex.MulStruct t s .const (0 : Fin 1)) :
    zeroMapComponent (Lt.boundary.map ≫ selfPullbackFiberInclusion p e) =
      zeroMapComponent (Ls.boundary.map ≫ selfPullbackFiberInclusion p e ≫ selfPullbackSwap p) := by
  obtain ⟨r, h₁, h₀⟩ := selfPullback_exists_inverse_edge p e Ls Lt m
  rw [← h₁, ← h₀]
  exact zeroMapComponent_edge r

/-- 概要：任意の連結射の代表に対し、自己 pullback の交換は基本群の逆元の代表を与える。
方針：Kan 複体の逆元の三角形を選び、その持ち上げを成分で比較する。
規約：底 B の Kan 性と p の fibration 性だけを使う。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5。収縮可能な全空間の場合の交換の逆元表示。 -/
theorem selfPullback_swap_inverse_representative {E B : SSet.{u}} (p : E ⟶ B)
    [Fibration p] [KanComplex B] (e : E _⦋0⦌)
    (s : B.PtSimplex 1 (p.app _ e)) (Ls : BoundaryLift p e s) :
    ∃ (t : B.PtSimplex 1 (p.app _ e)) (Lt : BoundaryLift p e t),
      KanHomotopyGroup.mk t = (KanHomotopyGroup.mk s)⁻¹ ∧
      zeroMapComponent (Lt.boundary.map ≫ selfPullbackFiberInclusion p e) =
        zeroMapComponent
          (Ls.boundary.map ≫ selfPullbackFiberInclusion p e ≫ selfPullbackSwap p) := by
  obtain ⟨t, ⟨m⟩⟩ := PtSimplex.MulStruct.exists_left_inverse s (0 : Fin 1)
  let Lt := chooseBoundaryLift p e t
  refine ⟨t, Lt, ?_, selfPullback_inverse_components p e Ls Lt m⟩
  exact eq_inv_of_mul_eq_one_left (KanHomotopyGroup.mul_eq m)

end

end SerrePositivity.KST.Spectra
