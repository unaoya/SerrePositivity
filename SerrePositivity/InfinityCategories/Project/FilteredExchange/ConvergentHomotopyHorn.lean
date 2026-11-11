module
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.HomotopyTriangleEdges

/-!
概要：指定された二つの共通終点を持つ全円柱を二次外ホーン上へ厳密に貼る。
方針：ホーンの二辺の押し出しをパラメータとの積で送り、共通終点で貼り合わせる。
規約：区間変数を左へ移すだけで、元の二円柱を保持する。
使われ方：指定部分三角形を保つ共通終点を持つ相対比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {K X : SSet.{u}} {f₀ f₁ f₂ : K ⟶ X}
  (U : SSet.Homotopy f₀ f₂) (V : SSet.Homotopy f₁ f₂)

/-- 概要：二つの指定円柱は共通頂点上で厳密に一致する。
方針：区間の端点を評価する。
規約：U と V の共通終点。使われ方：二次外ホーンの二辺の貼り合わせ。 -/
lemma convergentHomotopyHorn_compatible :
    (stdSimplex.δ (0 : Fin 2) ▷ K) ≫ (β_ (Δ[1] : SSet.{u}) K).hom ≫ U.h =
      (stdSimplex.δ (0 : Fin 2) ▷ K) ≫ (β_ (Δ[1] : SSet.{u}) K).hom ≫ V.h := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalVertex_one_tensor]
  change snd (Δ[0] : SSet.{u}) K ≫ SSet.ι₁ ≫ U.h =
    snd (Δ[0] : SSet.{u}) K ≫ SSet.ι₁ ≫ V.h
  rw [U.h₁, V.h₁]

/-- 概要：元の二つの全円柱を共通終点を持つ二次外ホーンの図式。
方針：二辺の押し出しを使う。
規約：元の U・V の全円柱。使われ方：相対比較の補正の充填の入力。 -/
def convergentHomotopyHorn : (horn 2 2 : SSet.{u}) ⊗ K ⟶ X :=
  (horn₂₂.isPushout.map (tensorRight K)).desc
    ((β_ (Δ[1] : SSet.{u}) K).hom ≫ U.h)
    ((β_ (Δ[1] : SSet.{u}) K).hom ≫ V.h) (convergentHomotopyHorn_compatible U V)

/-- 概要：ホーンの第一辺は元の第一円柱。
方針：押し出しの第一脚。規約：全時刻。使われ方：比較補正の元の始点側の保持。 -/
lemma convergentHomotopyHorn_first :
    (horn₂₂.ι₀₂ ▷ K) ≫ convergentHomotopyHorn U V =
      (β_ (Δ[1] : SSet.{u}) K).hom ≫ U.h :=
  (horn₂₂.isPushout.map (tensorRight K)).inl_desc _ _ _

/-- 概要：ホーンの第二辺は元の第二円柱。
方針：押し出しの第二脚。規約：全時刻。使われ方：比較補正の元の終点側の保持。 -/
lemma convergentHomotopyHorn_last :
    (horn₂₂.ι₁₂ ▷ K) ≫ convergentHomotopyHorn U V =
      (β_ (Δ[1] : SSet.{u}) K).hom ≫ V.h :=
  (horn₂₂.isPushout.map (tensorRight K)).inr_desc _ _ _

end SerrePositivity.InfinityCategories.Project.FilteredExchange
