module

public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
概要：二次元内ホーンの二つの区間を、同じ任意の底上の pushout に束ねる。
方針：元のホーンの pushout の可換式を、その底への射と合成する。
規約：共有頂点と二つの元の区間の包含を厳密に保持する。
使われ方：元の分類 Hom の両側で同じ区間の貼り合わせを使う。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
namespace InnerTwoHornOver

variable {B : SSet.{u}} (h : (Λ[2, 1] : SSet.{u}) ⟶ B)

/-- 二つの区間を貼った元のホーン。 -/
def apex : Over B := Over.mk h

/-- 最初の区間。 -/
def first : Over B := Over.mk (horn₂₁.ι₀₁ ≫ h)

/-- 次の区間。 -/
def second : Over B := Over.mk (horn₂₁.ι₁₂ ≫ h)

/-- 二つの区間が共有する元の頂点。 -/
def vertex : Over B := Over.mk (stdSimplex.δ (0 : Fin 2) ≫ horn₂₁.ι₀₁ ≫ h)

/-- 共有頂点を最初の区間の終点として含める。 -/
def toFirst : vertex h ⟶ first h := Over.homMk (stdSimplex.δ (0 : Fin 2)) rfl

/-- 共有頂点を次の区間の始点として含める。 -/
def toSecond : vertex h ⟶ second h :=
  Over.homMk (stdSimplex.δ (1 : Fin 2)) (by
    change stdSimplex.δ (1 : Fin 2) ≫ (horn₂₁.ι₁₂ ≫ h) =
      stdSimplex.δ (0 : Fin 2) ≫ (horn₂₁.ι₀₁ ≫ h)
    rw [← Category.assoc, ← Category.assoc, horn₂₁.isPushout.w])

/-- 最初の区間の元の包含。 -/
def firstInclusion : first h ⟶ apex h := Over.homMk horn₂₁.ι₀₁ rfl

/-- 次の区間の元の包含。 -/
def secondInclusion : second h ⟶ apex h := Over.homMk horn₂₁.ι₁₂ rfl

/-- 底上で使う同じ四射の、基礎の pushout 表示。 -/
lemma isPushout : IsPushout (toFirst h).left (toSecond h).left
    (firstInclusion h).left (secondInclusion h).left := horn₂₁.isPushout

instance : Mono (toSecond h).left := inferInstanceAs (Mono (stdSimplex.δ (1 : Fin 2)))

end InnerTwoHornOver
end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
