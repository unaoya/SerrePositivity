module
public import SerrePositivity.KST.SConstruction.ConcreteCubeDimensionIso

/-! # 元の具体的連結積の構造同型の自然性
概要：結合同型と左右単位は、元の全ての具体的な射について自然となる。
方針：元の二・三ブロック連結の全頂点で評価し、忠実な頂点関数で判定する。
規約：座標反転は行わない。使われ方：連結積のモノイダル圏への束ね。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の連結積の結合同型は、全ての三つの具体的射について自然。 -/
lemma concreteCubeAssociator_naturality {X X' Y Y' Z Z' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    concreteCubeTensorMap (concreteCubeTensorMap f g) h ≫
        (concreteCubeAssociator X' Y' Z').hom =
      (concreteCubeAssociator X Y Z).hom ≫
        concreteCubeTensorMap f (concreteCubeTensorMap g h) := by
  apply Subtype.ext
  apply cubeVertex_eq_of_tripleJoin
  intro x y z
  change (concreteCubeAssociator X' Y' Z').hom.val
      ((concreteCubeTensorMap (concreteCubeTensorMap f g) h).val
        (cubeVertexJoin (cubeVertexJoin x y) z)) =
    (concreteCubeTensorMap f (concreteCubeTensorMap g h)).val
      ((concreteCubeAssociator X Y Z).hom.val (cubeVertexJoin (cubeVertexJoin x y) z))
  erw [concreteCubeTensorMap_join, concreteCubeTensorMap_join, concreteCubeAssociator_join,
    concreteCubeAssociator_join, concreteCubeTensorMap_join, concreteCubeTensorMap_join]
  rfl

/-- 左単位同型は元の全ての具体的射について自然。 -/
lemma concreteCubeLeftUnitor_naturality {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ Y) :
    concreteCubeTensorMap (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0)) f ≫ (concreteCubeLeftUnitor Y).hom =
      (concreteCubeLeftUnitor X).hom ≫ f := by
  apply Subtype.ext
  funext v
  have hv := cubeVertexJoin_parts (n := 0) (m := X.dimension) v
  rw [← hv]
  change (concreteCubeLeftUnitor Y).hom.val
      ((concreteCubeTensorMap (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0)) f).val
        (cubeVertexJoin (cubeVertexLeftPart X.dimension v)
          (cubeVertexRightPart 0 X.dimension v))) =
    f.val ((concreteCubeLeftUnitor X).hom.val
      (cubeVertexJoin (cubeVertexLeftPart X.dimension v)
        (cubeVertexRightPart 0 X.dimension v)))
  erw [concreteCubeTensorMap_join, concreteCubeLeftUnitor_join, concreteCubeLeftUnitor_join]

/-- 右単位同型は元の全ての具体的射について自然。 -/
lemma concreteCubeRightUnitor_naturality {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ Y) :
    concreteCubeTensorMap f (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0)) ≫ (concreteCubeRightUnitor Y).hom =
      (concreteCubeRightUnitor X).hom ≫ f := by
  rfl

end SerrePositivity.KST.SConstruction
