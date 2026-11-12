module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingFaceEndpoints
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.CompositionTriangleSpace

/-!
概要：対角を全 Hom 空間で動かし、終域辺を固定した同じ外ホーンの族。
方針：対角の普遍区間族と指定終域辺を、共通の終点で貼り合わせる。
規約：対角の全高次と元の指定辺を保持する。
使われ方：合成三角形の対角評価を外ホーン制限の pullback として表示する。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

variable {X : SSet.{u}} (x : X _⦋0⦌) {y z : X _⦋0⦌} (g : X.Edge y z)
local notation "H" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x z

/-- 対角の全 Hom の普遍族と同じ指定終域辺を、元の外ホーンへ貼る。 -/
def cospanHomHornDiagram : (horn 2 2 : SSet.{u}) ⊗ H ⟶ X :=
  (horn₂₂.isPushout.map (tensorRight H)).desc
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (𝟙 H))
    (fst (Δ[1] : SSet.{u}) H ≫ SSet.yonedaEquiv.symm g.edge) (by
      change (stdSimplex.δ (0 : Fin 2) ▷ H) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (𝟙 H) =
        (stdSimplex.δ (0 : Fin 2) ▷ H) ≫ fst (Δ[1] : SSet.{u}) H ≫
          SSet.yonedaEquiv.symm g.edge
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_face_target, ← Category.assoc, whiskerRight_fst,
        Category.assoc, g.δ_zero_yonedaEquiv_symm])

/-- 同じ外ホーンの対角は、元の Hom 空間の普遍区間族。 -/
lemma cospanHomHornDiagram_diagonal :
    (horn₂₂.ι₀₂ ▷ H) ≫ cospanHomHornDiagram x g = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (𝟙 H) :=
  (horn₂₂.isPushout.map (tensorRight H)).inl_desc _ _ _

/-- 同じ外ホーンの終域辺は、元の指定辺に定値。 -/
lemma cospanHomHornDiagram_target :
    (horn₂₂.ι₁₂ ▷ H) ≫ cospanHomHornDiagram x g =
      fst (Δ[1] : SSet.{u}) H ≫ SSet.yonedaEquiv.symm g.edge :=
  (horn₂₂.isPushout.map (tensorRight H)).inr_desc _ _ _

/-- 対角の Hom 空間から、同じ可変外ホーンの関手空間への族。 -/
def cospanHomHornMap : H ⟶ (ihom (horn 2 2 : SSet.{u})).obj X :=
  curry (cospanHomHornDiagram x g)

/-- 任意の対角の族で、同じ外ホーンの対角は元の区間族そのもの。 -/
lemma cospanHomHornMap_diagonal {T : SSet.{u}} (a : T ⟶ H) :
    (horn₂₂.ι₀₂ ▷ T) ≫ uncurry (a ≫ cospanHomHornMap x g) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry a := by
  rw [uncurry_natural_left, cospanHomHornMap, uncurry_curry, ← Category.assoc,
    ← whisker_exchange, Category.assoc, cospanHomHornDiagram_diagonal,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, Category.comp_id]

/-- 任意の対角の族でも、同じ外ホーンの終域辺は元の指定辺に定値。 -/
lemma cospanHomHornMap_target {T : SSet.{u}} (a : T ⟶ H) :
    (horn₂₂.ι₁₂ ▷ T) ≫ uncurry (a ≫ cospanHomHornMap x g) =
      fst (Δ[1] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm g.edge := by
  rw [uncurry_natural_left, cospanHomHornMap, uncurry_curry, ← Category.assoc,
    ← whisker_exchange, Category.assoc, cospanHomHornDiagram_target,
    ← Category.assoc, whiskerLeft_fst]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
