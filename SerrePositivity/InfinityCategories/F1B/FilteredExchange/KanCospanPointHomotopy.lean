module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.CoproductConstantCylinder
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.CoproductCylinderMap
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.CylinderBoundaryMono
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalPullbackHomotopyPoint
public import SerrePositivity.InfinityCategories.F1B.FilteredExchange.KanCospanBoundarySquare
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.KanCospanPathEndpoints
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.KanCospanPoint
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.PathSquareCurry

/-!
概要：元の二入力と指定 path の全正方形を Kan 引き戻し内の比較へ移す。
方針：端点表示を両方向に移し、三座標を保持した正方形の持ち上げを使う。
規約：終端 path の全円柱も入力の全輸送も保持する。
使われ方：有限近似・同時輸送・元の値への反映を同じ引き戻し内で合成する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の入力の全境界輸送を持つ正方形は指定 Kan 引き戻し射の比較を与える。
方針：既存の持ち上げの終端を元の端点表示へ戻す。
規約：全円柱と三座標を保持。使われ方：同時輸送の二段の比較の接続。 -/
lemma kanCospanPoint_homotopy_of_square {K E D X : SSet.{u}}
    (f : E ⟶ X) (g : D ⟶ X) {u₀ u₁ : K ⟶ E} {v₀ v₁ : K ⟶ D}
    (H₀ : SSet.Homotopy (u₀ ≫ f ≫ continuousKanReplacementUnit.app X)
      (v₀ ≫ g ≫ continuousKanReplacementUnit.app X))
    (U : SSet.Homotopy u₀ u₁) (V : SSet.Homotopy v₀ v₁)
    {b : K ⊗ (Δ[1] : SSet.{u}) ⟶ continuousKanReplacement.obj X}
    (G : SSet.Homotopy H₀.h b)
    (hG : (cylinderBoundaryInclusion K ▷ (Δ[1] : SSet.{u})) ≫ G.h =
      coprodCylinderMap (U.h ≫ f) (V.h ≫ g) ≫ continuousKanReplacementUnit.app X) :
    ∃ H₁ : SSet.Homotopy (u₁ ≫ f ≫ continuousKanReplacementUnit.app X)
      (v₁ ≫ g ≫ continuousKanReplacementUnit.app X), H₁.h = b ∧
      ∃ L : SSet.Homotopy (kanCospanPoint f g u₀ v₀ H₀) (kanCospanPoint f g u₁ v₁ H₁),
        L.h ≫ intervalPullbackLeft (continuousKanReplacement.map f)
          (continuousKanReplacement.map g) = U.h ≫ continuousKanReplacementUnit.app E ∧
        L.h ≫ intervalPullbackRight (continuousKanReplacement.map f)
          (continuousKanReplacement.map g) = V.h ≫ continuousKanReplacementUnit.app D ∧
        L.h ≫ intervalPullbackPath (continuousKanReplacement.map f)
          (continuousKanReplacement.map g) = pathSquareCurry G.h := by
  obtain ⟨H₁, h₁, L, hl, hr, hp⟩ := kanCospan_pullback_homotopy_of_square f g H₀ U V G hG
  exact ⟨kanCospanRawPath f g u₁ v₁ H₁, h₁, L, hl, hr, hp⟩

/-- 概要：端点固定の指定 path 比較は同じ入力の Kan 引き戻し射のホモトピーを与える。
方針：二入力の定値円柱の貼り合わせを境界に指定する。
規約：元の二つの指定 path を比較。使われ方：有限近似と値への反映の接続。 -/
lemma kanCospanPoint_homotopy_of_fixed_boundary {K E D X : SSet.{u}}
    (f : E ⟶ X) (g : D ⟶ X) (u : K ⟶ E) (v : K ⟶ D)
    (H₀ H₁ : SSet.Homotopy (u ≫ f ≫ continuousKanReplacementUnit.app X)
      (v ≫ g ≫ continuousKanReplacementUnit.app X))
    (G : SSet.Homotopy H₀.h H₁.h)
    (hG : (cylinderBoundaryInclusion K ▷ (Δ[1] : SSet.{u})) ≫ G.h =
      fst (K ⨿ K) (Δ[1] : SSet.{u}) ≫ coprod.desc (u ≫ f) (v ≫ g) ≫
        continuousKanReplacementUnit.app X) :
    Nonempty (SSet.Homotopy (kanCospanPoint f g u v H₀) (kanCospanPoint f g u v H₁)) := by
  have h : (cylinderBoundaryInclusion K ▷ (Δ[1] : SSet.{u})) ≫ G.h =
      coprodCylinderMap ((functorHomotopyRefl u).h ≫ f) ((functorHomotopyRefl v).h ≫ g) ≫
        continuousKanReplacementUnit.app X := by
    dsimp only [functorHomotopyRefl]
    simpa only [Category.assoc, coprodCylinderMap_constant] using hG
  obtain ⟨J, hJ, L, _, _, _⟩ := kanCospanPoint_homotopy_of_square f g H₀
    (functorHomotopyRefl u) (functorHomotopyRefl v) G h
  have he := kanCospanPoint_congr f g u v J H₁ hJ
  rw [he] at L
  exact ⟨L⟩

end SerrePositivity.InfinityCategories.F2
