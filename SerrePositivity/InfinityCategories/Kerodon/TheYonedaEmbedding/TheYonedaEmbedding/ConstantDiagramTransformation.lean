module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantTransformationPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeSquareParameters
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.TransformationFamilyDiagram

/-!
概要：元の圏内の区間の族を、定値図式の間の変換の族へ厳密に移す。
方針：図式のパラメータを忘れた円柱を二端固定で curry する。
規約：元の区間の族と指定した両頂点を保つ。
使われ方：全 Hom 三角形の第二辺の定値図式としての正規化。

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
variable {X T : SSet.{u}} {x y : X _⦋0⦌}

/-- 概要：区間の全族を、同じ両頂点の定値図式の変換の族として表示する。
方針：図式の成分を忘れた円柱を curry する。
規約：全高次パラメータを保つ。使われ方：三角形の第二変換。 -/
def constantDiagramTransformation (K : SSet.{u}) (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x : K ⟶ X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantTransformationCurry ((snd K (Δ[1] : SSet.{u}) ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry a)
  · have h : (SSet.ι₀ (X := K) ▷ T) ≫ (snd K (Δ[1] : SSet.{u}) ▷ T) =
        snd K T ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 T := rfl
    rw [← Category.assoc, h, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_zero, SSet.comp_const]
    rw [SSet.comp_const]
  · have h : (SSet.ι₁ (X := K) ▷ T) ≫ (snd K (Δ[1] : SSet.{u}) ▷ T) =
        snd K T ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 T := rfl
    rw [← Category.assoc, h, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_one, SSet.comp_const]

/-- 概要：定値図式の変換の円柱は元の区間の族から図式の成分を忘れたもの。
方針：二端固定 curry の往復。規約：厳密な式。使われ方：第二辺の照合。 -/
lemma constantDiagramTransformation_prism (K : SSet.{u}) (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantTransformationPrism (constantDiagramTransformation K a) =
      (snd K (Δ[1] : SSet.{u}) ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantTransformationPrism_curry _ _ _

/-- 概要：空間値の定値図式間の変換の全図式は元の区間の族の座標表示そのもの。
方針：円柱の厳密な式を coherent な族の座標へ移す。
規約：全時刻・全パラメータ。使われ方：全 Hom 三角形の第二辺。 -/
lemma constantDiagramTransformation_diagram {B A : SSet.{u + 1}}
    {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌} (a : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace s t) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram (constantDiagramTransformation B a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeVerticalParameters B A ≫ snd B (A ⊗ (Δ[1] : SSet.{u + 1})) ≫
        (β_ A (Δ[1] : SSet.{u + 1})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry a := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeHorizontalParameters B A ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantTransformationPrism (constantDiagramTransformation B a) = _
  rw [constantDiagramTransformation_prism]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
