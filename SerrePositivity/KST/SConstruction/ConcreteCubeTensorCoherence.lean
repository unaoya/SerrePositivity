module
public import SerrePositivity.KST.SConstruction.ConcreteCubeTensorNaturality

/-! # 元の具体的連結積の五角と三角
概要：同じ順序の次元移送から、結合同型の五角と左右単位の三角を証明する。
方針：元の tensor 射による等号移送の保存と、eqToHom の合成則を使う。
規約：頂点の順序を保つ同じ構造射を使う。使われ方：具体的立方体圏のモノイダル構造。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の結合同型は連結積の五角を満たす。 -/
lemma concreteCubeAssociator_pentagon (W X Y Z : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    concreteCubeTensorMap (concreteCubeAssociator W X Y).hom (𝟙 Z) ≫
        (concreteCubeAssociator W (concreteCubeTensorObj X Y) Z).hom ≫
          concreteCubeTensorMap (𝟙 W) (concreteCubeAssociator X Y Z).hom =
      (concreteCubeAssociator (concreteCubeTensorObj W X) Y Z).hom ≫
        (concreteCubeAssociator W X (concreteCubeTensorObj Y Z)).hom := by
  simp only [concreteCubeAssociator, concreteCubeDimensionIso, eqToIso.hom,
    ← eqToHom_refl, concreteCubeTensorMap_eqToHom, eqToHom_trans]

/-- 元の結合同型と左右単位は連結積の三角を満たす。 -/
lemma concreteCubeAssociator_triangle (X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    (concreteCubeAssociator X (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) Y).hom ≫
        concreteCubeTensorMap (𝟙 X) (concreteCubeLeftUnitor Y).hom =
      concreteCubeTensorMap (concreteCubeRightUnitor X).hom (𝟙 Y) := by
  simp only [concreteCubeAssociator, concreteCubeLeftUnitor, concreteCubeRightUnitor,
    concreteCubeDimensionIso, eqToIso.hom, ← eqToHom_refl, concreteCubeTensorMap_eqToHom,
    eqToHom_trans]

end SerrePositivity.KST.SConstruction
