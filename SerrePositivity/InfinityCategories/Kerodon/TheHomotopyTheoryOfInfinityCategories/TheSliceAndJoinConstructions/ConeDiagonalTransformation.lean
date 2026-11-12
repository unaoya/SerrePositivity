module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeDiagonalPrismHomotopy
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.SourceConstantTransformationHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeTransformationMap
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.TransformationFamilyDiagram

/-!
概要：元の三角形の対角を変換空間へ戻し、元の錐の全 Hom の標準変換と比較する。
方針：両端固定の円柱の最小値変形を全パラメータで curry する。
規約：元の図式・指定頂点・全 Hom の族を保持する。
使われ方：指定三角形による全空間比較の長辺を実際の錐比較へ戻す。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

variable {K X : SSet.{u}} [Quasicategory X] {f : K ⟶ X}

/-- 概要：元の正方形の対角を同じ両端の変換の族へ戻す。
方針：元の対角の円柱を二端固定で curry する。
規約：元の対角そのもの。使われ方：指定三角形の長辺の変換。 -/
def coneDiagonalTransformation (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone f) (z : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom z c.vertex ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const z)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.sourceConstantTransformationCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneDiagonalPrism c z)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneDiagonalPrism_zero c z) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneDiagonalPrism_one c z)

/-- 概要：対角の変換を円柱に戻すと元の対角。
方針：二端固定 curry の往復。規約：厳密な一致。使われ方：三角形との照合。 -/
lemma coneDiagonalTransformation_prism (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone f) (z : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.sourceConstantTransformationPrism (coneDiagonalTransformation c z) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneDiagonalPrism c z :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.sourceConstantTransformationPrism_curry _ _ _

/-- 概要：対角の変換と元の全 Hom の錐族の標準変換を実際のホモトピーで結ぶ。
方針：最小値変形の全円柱を固定した二端とともに変換空間へ戻す。
規約：全 Hom の全高次パラメータ。使われ方：合成則の長辺の比較。 -/
def coneDiagonalTransformationHomotopy (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone f) (z : X _⦋0⦌) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.fixedApexConeHomComparison c z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneTransformationMap f z)
      (coneDiagonalTransformation c z) := by
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneDiagonalPrismHomotopy c z
  have ha := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneTransformationMap_prism (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.fixedApexConeHomComparison c z)
  have hb := coneDiagonalTransformation_prism c z
  let H' : SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.sourceConstantTransformationPrism
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.fixedApexConeHomComparison c z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneTransformationMap f z))
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.sourceConstantTransformationPrism (coneDiagonalTransformation c z)) :=
    ⟨H.h, H.h₀.trans ha.symm, H.h₁.trans hb.symm, H.rel⟩
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.sourceConstantTransformationHomotopyOfPrisms _ _ H'
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneDiagonalPrismHomotopy_left c z) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneDiagonalPrismHomotopy_right c z)

/-- 概要：空間値の元の全 Hom 三角形の長辺は対角の変換の族そのもの。
方針：元の三角形の対角の円柱を coherent な族の座標へ移す。
規約：全パラメータで厳密な一致。使われ方：unstraightening の合成則の長辺。 -/
lemma conePointHomTriangle_diagonal_transformation
    {B : SSet.{u + 1}} {F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F) (z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom z c.vertex)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.conePointHomTriangle c z =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram (coneDiagonalTransformation c z) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneDiagonalPrism_triangle, ← coneDiagonalTransformation_prism]
  apply SSet.hom_ext
  intro n
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
