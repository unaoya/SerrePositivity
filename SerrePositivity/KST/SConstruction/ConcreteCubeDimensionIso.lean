module
public import SerrePositivity.KST.SConstruction.ConcreteCubeTensor
public import SerrePositivity.KST.SConstruction.CubeVertexTransport

/-! # 次元の等号による具体的立方体の構造同型
概要：連結積の結合・左右単位を、次元の等号から得る実際の射として構成する。
方針：対象の等号の eqToIso を使い、元の頂点座標の移送を回収する。
規約：構造射は同じ順序の座標を保持する。使われ方：連結積のモノイダル構造。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 次元の等号から得られる、具体的立方体の元の構造同型。 -/
def concreteCubeDimensionIso {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (h : X.dimension = Y.dimension) : X ≅ Y :=
  eqToIso (by cases X; cases Y; cases h; rfl)

/-- 構造同型の元の頂点関数は、同じ次元移送。 -/
lemma concreteCubeDimensionIso_hom_val {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube}
    (h : X.dimension = Y.dimension) (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex X.dimension) :
    (concreteCubeDimensionIso h).hom.val x = cubeVertexCast h x := by
  cases X
  cases Y
  cases h
  rfl

/-- 元の連結積の結合同型。 -/
def concreteCubeAssociator (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    concreteCubeTensorObj (concreteCubeTensorObj X Y) Z ≅
      concreteCubeTensorObj X (concreteCubeTensorObj Y Z) :=
  concreteCubeDimensionIso (Nat.add_assoc X.dimension Y.dimension Z.dimension)

/-- 元の零次元立方体を左単位とする同型。 -/
def concreteCubeLeftUnitor (X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    concreteCubeTensorObj (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) X ≅ X :=
  concreteCubeDimensionIso (Nat.zero_add X.dimension)

/-- 元の零次元立方体を右単位とする同型。 -/
def concreteCubeRightUnitor (X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    concreteCubeTensorObj X (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) ≅ X := concreteCubeDimensionIso rfl

/-- 連結積は両因子の対象等号による移送を保持する。 -/
lemma concreteCubeTensorMap_eqToHom {X X' Y Y' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (h : X = X') (k : Y = Y') :
    concreteCubeTensorMap (eqToHom h) (eqToHom k) =
      eqToHom (congrArg₂ concreteCubeTensorObj h k) := by
  cases h
  cases k
  exact concreteCubeTensorMap_id X Y

/-- 結合同型は三つの元の頂点の同じ順序を回収する。 -/
lemma concreteCubeAssociator_join (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube)
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex X.dimension) (y : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex Y.dimension) (z : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex Z.dimension) :
    (concreteCubeAssociator X Y Z).hom.val (cubeVertexJoin (cubeVertexJoin x y) z) =
      cubeVertexJoin x (cubeVertexJoin y z) :=
  (concreteCubeDimensionIso_hom_val _ _).trans (cubeVertexJoin_assoc x y z)

/-- 左単位は零次元ブロックの連結から元の頂点を回収する。 -/
lemma concreteCubeLeftUnitor_join (X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex 0)
    (y : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex X.dimension) :
    (concreteCubeLeftUnitor X).hom.val (cubeVertexJoin x y) = y :=
  (concreteCubeDimensionIso_hom_val _ _).trans (cubeVertexJoin_zero_left x y)

/-- 右単位の元の頂点関数は恒等写像。 -/
lemma concreteCubeRightUnitor_val (X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex X.dimension) :
    (concreteCubeRightUnitor X).hom.val x = x :=
  concreteCubeDimensionIso_hom_val rfl x

end SerrePositivity.KST.SConstruction
