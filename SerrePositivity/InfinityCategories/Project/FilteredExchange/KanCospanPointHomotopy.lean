module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoproductConstantCylinder
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoproductCylinderMap
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CylinderBoundaryMono
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalPullbackHomotopyPoint
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanCospanBoundarySquare
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanCospanPathEndpoints
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanCospanPoint
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.PathSquareCurry

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
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：元の入力の全境界輸送を持つ正方形は指定 Kan 引き戻し射の比較を与える。
方針：既存の持ち上げの終端を元の端点表示へ戻す。
規約：全円柱と三座標を保持。使われ方：同時輸送の二段の比較の接続。 -/
lemma kanCospanPoint_homotopy_of_square {K E D X : SSet.{u}}
    (f : E ⟶ X) (g : D ⟶ X) {u₀ u₁ : K ⟶ E} {v₀ v₁ : K ⟶ D}
    (H₀ : SSet.Homotopy (u₀ ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X)
      (v₀ ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X))
    (U : SSet.Homotopy u₀ u₁) (V : SSet.Homotopy v₀ v₁)
    {b : K ⊗ (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj X}
    (G : SSet.Homotopy H₀.h b)
    (hG : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.cylinderBoundaryInclusion K ▷ (Δ[1] : SSet.{u})) ≫ G.h =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coprodCylinderMap (U.h ≫ f) (V.h ≫ g) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X) :
    ∃ H₁ : SSet.Homotopy (u₁ ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X)
      (v₁ ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X), H₁.h = b ∧
      ∃ L : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanCospanPoint f g u₀ v₀ H₀) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanCospanPoint f g u₁ v₁ H₁),
        L.h ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g) = U.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E ∧
        L.h ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackRight (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g) = V.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app D ∧
        L.h ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackPath (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g) = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pathSquareCurry G.h := by
  obtain ⟨H₁, h₁, L, hl, hr, hp⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanCospan_pullback_homotopy_of_square f g H₀ U V G hG
  exact ⟨_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanCospanRawPath f g u₁ v₁ H₁, h₁, L, hl, hr, hp⟩

/-- 概要：端点固定の指定 path 比較は同じ入力の Kan 引き戻し射のホモトピーを与える。
方針：二入力の定値円柱の貼り合わせを境界に指定する。
規約：元の二つの指定 path を比較。使われ方：有限近似と値への反映の接続。 -/
lemma kanCospanPoint_homotopy_of_fixed_boundary {K E D X : SSet.{u}}
    (f : E ⟶ X) (g : D ⟶ X) (u : K ⟶ E) (v : K ⟶ D)
    (H₀ H₁ : SSet.Homotopy (u ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X)
      (v ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X))
    (G : SSet.Homotopy H₀.h H₁.h)
    (hG : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.cylinderBoundaryInclusion K ▷ (Δ[1] : SSet.{u})) ≫ G.h =
      fst (K ⨿ K) (Δ[1] : SSet.{u}) ≫ coprod.desc (u ≫ f) (v ≫ g) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X) :
    Nonempty (SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanCospanPoint f g u v H₀) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanCospanPoint f g u v H₁)) := by
  have h : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.cylinderBoundaryInclusion K ▷ (Δ[1] : SSet.{u})) ≫ G.h =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coprodCylinderMap ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl u).h ≫ f) ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl v).h ≫ g) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl]
    simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coprodCylinderMap_constant] using hG
  obtain ⟨J, hJ, L, _, _, _⟩ := kanCospanPoint_homotopy_of_square f g H₀
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl u) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl v) G h
  have he := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanCospanPoint_congr f g u v J H₁ hJ
  rw [he] at L
  exact ⟨L⟩

end SerrePositivity.InfinityCategories.Project.FilteredExchange
