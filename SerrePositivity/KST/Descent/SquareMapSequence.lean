module

public import SerrePositivity.KST.Descent.SquareSequence

/-!
# 幾何正方形の射による長完全列の比較

## 概要
可換な立方体の四頂点の引き戻しから、二つの正方形の指定制限と差の比較を構成する。
境界の自然性が与えられれば全次数の長完全列の射となる。

## 方針
各面の可換式へ反変前層を適用する。境界についてだけは別途その自然性を要求する。

## 規約
異なる前層の自然変換による比較と、異なる幾何正方形による比較を区別する。
境界は実降下から供給される写像を保持する。

## 使われ方
論文 補題 3.3・定理 3.1 の幾何的な引き戻しと、軌道正方形の自己同型。
-/

@[expose] public section

universe u v w t

open CategoryTheory Opposite

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] {Coefficient : Type w}
variable (L : GradedPresheaf.{u, v, w, t} C Coefficient) (H : Coefficient)
variable {sq tq : Square C}

/-- 概要：正方形の射が誘導する二つの部分の比較（論文 §3）。
方針：右上と左下の引き戻しの積を取る。
規約：反変の向きを保持する。
使われ方：Mayer–Vietoris 列の中項の指定比較。 -/
def GradedPresheaf.squareMapProduct (n : ℤ) (f : sq ⟶ tq) :
    ((L H n).obj (op tq.X₂) × (L H n).obj (op tq.X₃)) →ₗ[ℚ]
      ((L H n).obj (op sq.X₂) × (L H n).obj (op sq.X₃)) :=
  (L.pullback H n f.τ₂).prodMap (L.pullback H n f.τ₃)

/-- 概要：幾何正方形の射は指定制限と可換（論文 定理 3.1）。
方針：右面・下面の可換式に反変前層を適用する。
規約：制限写像を抽象的な同型へ取り替えない。
使われ方：全次数の列の比較の第一の可換式。 -/
theorem GradedPresheaf.squareMap_restriction (n : ℤ) (f : sq ⟶ tq) :
    (L.squareRestriction H n sq).comp (L.pullback H n f.τ₄) =
      (L.squareMapProduct H n f).comp (L.squareRestriction H n tq) := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · change L.pullback H n sq.f₂₄ (L.pullback H n f.τ₄ x) =
      L.pullback H n f.τ₂ (L.pullback H n tq.f₂₄ x)
    have h := congrArg (fun k ↦ L.pullback H n k x) f.comm₂₄
    simpa only [GradedPresheaf.pullback_comp, LinearMap.comp_apply] using h
  · change L.pullback H n sq.f₃₄ (L.pullback H n f.τ₄ x) =
      L.pullback H n f.τ₃ (L.pullback H n tq.f₃₄ x)
    have h := congrArg (fun k ↦ L.pullback H n k x) f.comm₃₄
    simpa only [GradedPresheaf.pullback_comp, LinearMap.comp_apply] using h

/-- 概要：幾何正方形の射は指定制限の差と可換（論文 定理 3.1）。
方針：上面・左面の可換式と線形性を用いる。
規約：正負の符号を含む既存の指定差を保持する。
使われ方：全次数の列の比較の第二の可換式。 -/
theorem GradedPresheaf.squareMap_difference (n : ℤ) (f : sq ⟶ tq) :
    (L.squareDifference H n sq).comp (L.squareMapProduct H n f) =
      (L.pullback H n f.τ₁).comp (L.squareDifference H n tq) := by
  apply LinearMap.ext
  intro x
  change L.pullback H n sq.f₁₂ (L.pullback H n f.τ₂ x.1) -
      L.pullback H n sq.f₁₃ (L.pullback H n f.τ₃ x.2) =
    L.pullback H n f.τ₁ (L.pullback H n tq.f₁₂ x.1 - L.pullback H n tq.f₁₃ x.2)
  rw [map_sub]
  congr 1
  · have h := congrArg (fun k ↦ L.pullback H n k x.1) f.comm₁₂
    simpa only [GradedPresheaf.pullback_comp, LinearMap.comp_apply] using h
  · have h := congrArg (fun k ↦ L.pullback H n k x.2) f.comm₁₃
    simpa only [GradedPresheaf.pullback_comp, LinearMap.comp_apply] using h

/-- 概要：自然な境界を持つ幾何正方形の射から全次数の列の射（論文 §3）。
方針：四頂点の引き戻しと、境界を含む三つの可換式を束ねる。
規約：境界の自然性は実降下の長完全列から供給する明示的な条件。
使われ方：軌道正方形の引き戻し・自己同型による比較。 -/
def SquareMayerVietoris.pullbackComparison
    (source : SquareMayerVietoris L H sq) (target : SquareMayerVietoris L H tq)
    (f : sq ⟶ tq)
    (boundary_naturality : ∀ n,
      (source.boundary n).comp (L.pullback H (n + 1) f.τ₁) =
        (L.pullback H n f.τ₄).comp (target.boundary n)) :
    GradedMayerVietoris.Hom target.toGraded source.toGraded where
  mapA n := L.pullback H n f.τ₄
  mapB n := L.squareMapProduct H n f
  mapC n := L.pullback H n f.τ₁
  comm_restriction n := L.squareMap_restriction H n f
  comm_difference n := L.squareMap_difference H n f
  comm_boundary := boundary_naturality

end SerrePositivity.KST.Descent
