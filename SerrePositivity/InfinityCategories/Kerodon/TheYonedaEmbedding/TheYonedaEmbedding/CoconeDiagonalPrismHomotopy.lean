module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeDiagonalPrism

/-!
概要：元の三角形の対角から元の全 Hom の余錐族への、図式・頂点を固定した円柱の変形。
方針：最大値によるパラメータの変形を元の正方形で評価する。
規約：全時刻で二端を固定する。
使われ方：対角の変換を元の標準余錐比較へ戻す。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

variable {K X : SSet.{u}} [Quasicategory X] {f : K ⟶ X}

/-- 概要：元の正方形の対角を元の全 Hom の余錐族の円柱へ変形する。
方針：横時刻を固定し、縦時刻を二時刻の最大値に変える。
規約：元の正方形を変更しない。使われ方：指定三角形の長辺の比較。 -/
def coconeDiagonalPrismHomotopy (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone f) (z : X _⦋0⦌) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeDiagonalPrism c z)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeParameterPrism (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily c z)) where
  h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeDiagonalDeformationParameters K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft c.vertex z) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconePointHomSquare c z
  h₀ := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeDiagonalDeformationParameters_zero]
    rfl
  h₁ := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeDiagonalDeformationParameters_one,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconePointHomSquare_target]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：円柱の変形の図式側の端点は全時刻で元の図式に固定。
方針：最大値の第一時刻零と正方形の横始点を計算する。
規約：全 Hom の族。使われ方：変換空間へ戻すための固定条件。 -/
lemma coconeDiagonalPrismHomotopy_left (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone f) (z : X _⦋0⦌) :
    ((SSet.ι₀ (X := K) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft c.vertex z) ▷ (Δ[1] : SSet.{u})) ≫
      (coconeDiagonalPrismHomotopy c z).h =
        fst (K ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft c.vertex z) Δ[1] ≫ fst K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft c.vertex z) ≫ f := by
  change _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeDiagonalDeformationParameters K _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconePointHomSquare c z) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeDiagonalDeformationParameters_left,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconePointHomSquare_zero]
  rfl

/-- 概要：円柱の変形の頂点側の端点は全時刻で元の指定頂点に固定。
方針：最大値の第一時刻一と正方形の上辺・その終点を計算する。
規約：指定頂点を変更しない。使われ方：変換空間のホモトピーの固定終点。 -/
lemma coconeDiagonalPrismHomotopy_right (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone f) (z : X _⦋0⦌) :
    ((SSet.ι₁ (X := K) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft c.vertex z) ▷ (Δ[1] : SSet.{u})) ≫
      (coconeDiagonalPrismHomotopy c z).h = SSet.const z := by
  change _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeDiagonalDeformationParameters K _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconePointHomSquare c z) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeDiagonalDeformationParameters_right,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconePointHomSquare_target, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeParameterPrism_one, SSet.comp_const]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
