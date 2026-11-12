module
public import SerrePositivity.KST.SConstruction.NecklaceCubeTensorComparison
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceWedgeMonoidal
public import SerrePositivity.KST.SConstruction.ConcreteCubeMonoidal
public import SerrePositivity.KST.SConstruction.ObjectEqualityMaps

/-! # 元の necklace と cube の tensor 比較の coherent 法則
概要：元の二変数 tensor 比較が、結合と一点単位を厳密に保つと示す。
方針：全ての元の構造射を対象等号の移送として照合する。
規約：元の比較を変更しない。使われ方：具体的 cube 値の強モノイダル関手。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の一点 necklace の cube は零次元。 -/
lemma necklacePoint_dimension : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint.{u}.down.dimension = 0 := by decide

/-- 元の零次元 cube と元の一点 necklace の cube との単位同型。 -/
def necklaceCubeUnitIso : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0 ≅ (necklaceConcreteCube.{u}).obj _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint :=
  concreteCubeDimensionIso necklacePoint_dimension.{u}.symm

/-- 元の cube tensor 比較は、元の native wedge の結合同型を保つ。 -/
lemma necklaceCubeTensor_associativity (T U V : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    concreteCubeTensorMap (necklaceCubeTensorIso T U).hom
        (𝟙 ((necklaceConcreteCube.{u}).obj V)) ≫
      (necklaceCubeTensorIso (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge T U) V).hom ≫
        necklaceConcreteCube.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator T U V).hom =
    (concreteCubeAssociator (necklaceConcreteCube.obj T) (necklaceConcreteCube.obj U)
      (necklaceConcreteCube.obj V)).hom ≫
      concreteCubeTensorMap (𝟙 (necklaceConcreteCube.obj T)) (necklaceCubeTensorIso U V).hom ≫
        (necklaceCubeTensorIso T (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge U V)).hom := by
  apply objectEqualityMap_eq
  · exact objectEqualityMap_comp
      (concreteCubeTensor_objectEqualityMap (concreteCubeDimensionIso_objectEqualityMap _)
        (objectEqualityMap_id _))
      (objectEqualityMap_comp (concreteCubeDimensionIso_objectEqualityMap _)
        (objectEqualityMap_map _ (objectEqualityMap_eqToHom
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklace_eq_of_shape (T.down.wedge_assoc U.down V.down)))))
  · exact objectEqualityMap_comp (concreteCubeDimensionIso_objectEqualityMap _)
      (objectEqualityMap_comp
        (concreteCubeTensor_objectEqualityMap (objectEqualityMap_id _)
          (concreteCubeDimensionIso_objectEqualityMap _))
        (concreteCubeDimensionIso_objectEqualityMap _))

/-- 元の cube tensor 比較と単位同型は、元の左単位を保つ。 -/
lemma necklaceCubeTensor_left_unitality (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    (concreteCubeLeftUnitor (necklaceConcreteCube.obj T)).hom =
      concreteCubeTensorMap necklaceCubeUnitIso.{u}.hom (𝟙 (necklaceConcreteCube.obj T)) ≫
        (necklaceCubeTensorIso _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint T).hom ≫
          necklaceConcreteCube.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceLeftUnitor T).hom := by
  apply objectEqualityMap_eq
  · exact concreteCubeDimensionIso_objectEqualityMap _
  · exact objectEqualityMap_comp
      (concreteCubeTensor_objectEqualityMap (concreteCubeDimensionIso_objectEqualityMap _)
        (objectEqualityMap_id _))
      (objectEqualityMap_comp (concreteCubeDimensionIso_objectEqualityMap _)
        (objectEqualityMap_map _ (objectEqualityMap_eqToHom
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklace_eq_of_shape T.down.single_zero_wedge))))

/-- 元の cube tensor 比較と単位同型は、元の右単位を保つ。 -/
lemma necklaceCubeTensor_right_unitality (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    (concreteCubeRightUnitor (necklaceConcreteCube.obj T)).hom =
      concreteCubeTensorMap (𝟙 (necklaceConcreteCube.obj T)) necklaceCubeUnitIso.{u}.hom ≫
        (necklaceCubeTensorIso T _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint).hom ≫
          necklaceConcreteCube.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceRightUnitor T).hom := by
  apply objectEqualityMap_eq
  · exact concreteCubeDimensionIso_objectEqualityMap _
  · exact objectEqualityMap_comp
      (concreteCubeTensor_objectEqualityMap (objectEqualityMap_id _)
        (concreteCubeDimensionIso_objectEqualityMap _))
      (objectEqualityMap_comp (concreteCubeDimensionIso_objectEqualityMap _)
        (objectEqualityMap_map _ (objectEqualityMap_eqToHom
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklace_eq_of_shape T.down.wedge_single_zero))))

end SerrePositivity.KST.SConstruction
