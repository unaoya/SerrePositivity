module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingFaceEndpoints
public import SerrePositivity.InfinityCategories.F1.Diagrams.CompositionTriangleSpace

/-!
概要：第一辺が全 Hom 空間を動き、第二辺を固定した同じ内ホーンの族。
方針：区間 Hom の普遍族と指定第二辺を、共通の端点で貼り合わせる。
規約：第一辺の全高次を保持し、合成辺は選ばない。
使われ方：後合成と三角形延長の比較に使う、合成三角形全体の空間。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {X : SSet.{u}} (x : X _⦋0⦌) {y z : X _⦋0⦌} (g : X.Edge y z)
local notation "H" => intervalMappingSpace x y

/-- 第一辺の全 Hom の普遍族と同じ指定第二辺を、元の内ホーンへ貼る。 -/
def composableHomHornDiagram : (horn 2 1 : SSet.{u}) ⊗ H ⟶ X :=
  (horn₂₁.isPushout.map (tensorRight H)).desc
    (intervalMappingUncurry (𝟙 H))
    (fst (Δ[1] : SSet.{u}) H ≫ SSet.yonedaEquiv.symm g.edge) (by
      change (stdSimplex.δ (0 : Fin 2) ▷ H) ≫ intervalMappingUncurry (𝟙 H) =
        (stdSimplex.δ (1 : Fin 2) ▷ H) ≫ fst (Δ[1] : SSet.{u}) H ≫
          SSet.yonedaEquiv.symm g.edge
      rw [intervalMappingUncurry_face_target, ← Category.assoc, whiskerRight_fst,
        Category.assoc, g.δ_one_yonedaEquiv_symm])

/-- 同じ内ホーンの第一辺は、元の Hom 空間の普遍区間族。 -/
lemma composableHomHornDiagram_first :
    (horn₂₁.ι₀₁ ▷ H) ≫ composableHomHornDiagram x g = intervalMappingUncurry (𝟙 H) :=
  (horn₂₁.isPushout.map (tensorRight H)).inl_desc _ _ _

/-- 同じ内ホーンの第二辺は、元の指定第二辺に定値。 -/
lemma composableHomHornDiagram_last :
    (horn₂₁.ι₁₂ ▷ H) ≫ composableHomHornDiagram x g =
      fst (Δ[1] : SSet.{u}) H ≫ SSet.yonedaEquiv.symm g.edge :=
  (horn₂₁.isPushout.map (tensorRight H)).inr_desc _ _ _

/-- 第一辺の Hom 空間から、同じ可変内ホーンの関手空間への族。 -/
def composableHomHornMap : H ⟶ (ihom (horn 2 1 : SSet.{u})).obj X :=
  curry (composableHomHornDiagram x g)

/-- 任意の第一辺の族で、同じ内ホーンの第一辺は元の区間族そのもの。 -/
lemma composableHomHornMap_first {T : SSet.{u}} (a : T ⟶ H) :
    (horn₂₁.ι₀₁ ▷ T) ≫ uncurry (a ≫ composableHomHornMap x g) =
      intervalMappingUncurry a := by
  rw [uncurry_natural_left, composableHomHornMap, uncurry_curry, ← Category.assoc,
    ← whisker_exchange, Category.assoc, composableHomHornDiagram_first,
    ← intervalMappingUncurry_precomp, Category.comp_id]

/-- 任意の第一辺の族でも、同じ内ホーンの第二辺は元の指定辺に定値。 -/
lemma composableHomHornMap_last {T : SSet.{u}} (a : T ⟶ H) :
    (horn₂₁.ι₁₂ ▷ T) ≫ uncurry (a ≫ composableHomHornMap x g) =
      fst (Δ[1] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm g.edge := by
  rw [uncurry_natural_left, composableHomHornMap, uncurry_curry, ← Category.assoc,
    ← whisker_exchange, Category.assoc, composableHomHornDiagram_last,
    ← Category.assoc, whiskerLeft_fst]

end SerrePositivity.InfinityCategories
