module

public import SerrePositivity.KST.Spectra.SquareTriangleCover

/-!
概要：正方形の二つの三角形の交わりは共通の対角辺。
方針：両三角形の座標の順序を比較し、座標が一致することを示す。
規約：全ての単体次数で対角辺の代表を構成する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3。三角形の pushout の pullback 条件。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SquareTriangles

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：三角形の頂点では σ₀ の値は σ₁ の値以下。
方針：三つの頂点で検査する。
規約：上側の三角形の座標の順序を表す。
使われ方：Goerss–Jardine I §7。二つの三角形の共通部分の計算。 -/
theorem sigma_zero_le_one (a : Fin 3) :
    (SimplexCategory.σ (0 : Fin 2)) a ≤ (SimplexCategory.σ (1 : Fin 2)) a := by
  fin_cases a <;> decide

/-- 概要：下側の三角形の包含も各単体次数で単射。
方針：成分を交換して上側の単射性へ戻す。
規約：退化単体も含む。
使われ方：Goerss–Jardine I §7。共通の対角辺の代表の識別。 -/
theorem lower_app_injective (d : ℕ) : Function.Injective (lower.{u}.app (Opposite.op ⦋d⦌)) := by
  intro s t h
  apply upper_app_injective d
  exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)

/-- 概要：二つの三角形で同じ正方形の単体を表せば、同じ対角辺から得られる。
方針：座標の二方向の順序から座標の一致を得て、各包含の単射性を使う。
規約：対角辺の向きは両方で同じ。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3。正方形の三角形の pullback 条件。 -/
theorem upper_lower_intersection (d : ℕ) (s t : (Δ[2] : SSet.{u}) _⦋d⦌)
    (h : upper.app _ s = lower.app _ t) :
    ∃ v : (Δ[1] : SSet.{u}) _⦋d⦌,
      (stdSimplex.δ (1 : Fin 3)).app _ v = s ∧
        (stdSimplex.δ (1 : Fin 3)).app _ v = t := by
  let v : (Δ[1] : SSet.{u}) _⦋d⦌ := (upper.app _ s).1
  have hcoord (r : Fin (d + 1)) : (upper.app _ s).1 r = (upper.app _ s).2 r := by
    have hfst := congrArg (fun z => z.1 r) h
    have hsnd := congrArg (fun z => z.2 r) h
    change (SimplexCategory.σ (0 : Fin 2)) (s r) =
      (SimplexCategory.σ (1 : Fin 2)) (t r) at hfst
    change (SimplexCategory.σ (1 : Fin 2)) (s r) =
      (SimplexCategory.σ (0 : Fin 2)) (t r) at hsnd
    change (SimplexCategory.σ (0 : Fin 2)) (s r) =
      (SimplexCategory.σ (1 : Fin 2)) (s r)
    apply le_antisymm (sigma_zero_le_one (s r))
    rw [hfst, hsnd]
    exact sigma_zero_le_one (t r)
  have hdiag : diagonal.app _ v = upper.app _ s := by
    apply Prod.ext
    · rfl
    · apply stdSimplex.ext
      intro r
      exact hcoord r
  have hu := ConcreteCategory.congr_hom (congrArg
    (fun f : (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⊗ Δ[1] =>
      f.app (Opposite.op ⦋d⦌)) upper_diagonal) v
  have hl := ConcreteCategory.congr_hom (congrArg
    (fun f : (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⊗ Δ[1] =>
      f.app (Opposite.op ⦋d⦌)) lower_diagonal) v
  refine ⟨v, upper_app_injective d (hu.trans hdiag),
    lower_app_injective d (hl.trans (hdiag.trans h))⟩

end SerrePositivity.KST.Spectra.SquareTriangles
