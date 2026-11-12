module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeDiagonalParameters
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConePointHomTriangle

/-!
概要：元の錐の Hom 三角形の長辺を、定値始域と図式を固定した全円柱として表示する。
方針：元の正方形の対角を評価し、両端を元の四辺の式へ戻す。
規約：元の対角と全 Hom の全パラメータを保持する。
使われ方：元の native な Hom 比較と長辺の変換の比較。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

variable {K X : SSet.{u}} [Quasicategory X] {f : K ⟶ X}

/-- 元の正方形の同じ対角を、全 Hom の円柱の族へ戻す。 -/
def coneDiagonalPrism (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone f) (z : X _⦋0⦌) :
    (K ⊗ (Δ[1] : SSet.{u})) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom z c.vertex ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneDiagonalParameters K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom z c.vertex) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.conePointHomSquare c z

/-- 対角の始点は同じ元の Hom の指定始点。 -/
lemma coneDiagonalPrism_zero (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone f) (z : X _⦋0⦌) :
    (SSet.ι₀ ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom z c.vertex) ≫ coneDiagonalPrism c z = SSet.const z := by
  change ((SSet.ι₀ ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom z c.vertex) ≫
    ((K ⊗ (Δ[1] : SSet.{u})) ◁ SSet.ι₀)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.conePointHomSquare c z = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.conePointHomSquare_source, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneParameterPrism_zero]

/-- 対角の終点は同じ元の図式。 -/
lemma coneDiagonalPrism_one (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone f) (z : X _⦋0⦌) :
    (SSet.ι₁ ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom z c.vertex) ≫ coneDiagonalPrism c z =
      fst K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom z c.vertex) ≫ f := by
  change ((K ◁ SSet.ι₁) ≫
    (SSet.ι₁ ▷ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom z c.vertex ⊗ (Δ[1] : SSet.{u})))) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.conePointHomSquare c z = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.conePointHomSquare_one]
  rfl

/-- 元の三角形の長辺は、同じ対角の円柱の座標表示。 -/
lemma coneDiagonalPrism_triangle (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone f) (z : X _⦋0⦌) :
    (stdSimplex.δ (1 : Fin 3) ▷ (K ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom z c.vertex)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.conePointHomTriangle c z =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeHorizontalParameters K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom z c.vertex) ≫ coneDiagonalPrism c z := by
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal.{u} = lift (𝟙 Δ[1]) (𝟙 Δ[1]) := by
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.conePointHomTriangle_diagonal, hd]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
