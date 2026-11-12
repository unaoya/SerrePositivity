module
public import SerrePositivity.KST.SConstruction.CubePathNaturality

/-! # 元の生成語の右端保持
概要：元の全生成射の座標を一つずらし、右端入力を保持する語の関手を構成する。
方針：元の quiver 上の作用を一文字の path へ送り、path 関手へ延長する。
規約：語の端点の次元を明示する。使われ方：右 tensor 比較の元の語での検証。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の三種の生成射の座標を一つずらす。 -/
def cubeGeneratorRightKeep : {n m : ℕ} → _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeGenerator n m → _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeGenerator (n + 1) (m + 1)
  | _, _, .face b n i => .face b (n + 1) i.succ
  | _, _, .degeneracy n i => .degeneracy (n + 1) i.succ
  | _, _, .connection n i => .connection (n + 1) i.succ

/-- 右端保持した元の生成射の一文字の語。 -/
def cubeWordRightKeepPrefunctor : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject ⥤q _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWords where
  obj X := ⟨X.dimension + 1⟩
  map {X Y} g := (show _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk (X.dimension + 1) ⟶
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk (Y.dimension + 1) from cubeGeneratorRightKeep g).toPath

/-- 元の全生成語に作用する右端保持関手。 -/
def cubeWordRightKeep : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWords ⥤ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWords := Paths.lift cubeWordRightKeepPrefunctor

/-- 元の一文字の語の右端保持は同じ座標をずらした一文字の語。 -/
lemma cubeWordRightKeep_generator {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject} (g : X ⟶ Y) :
    cubeWordRightKeep.map g.toPath =
      (show _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk (X.dimension + 1) ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk (Y.dimension + 1) from
        cubeGeneratorRightKeep g).toPath :=
  Paths.lift_toPath _ g

/-- 元の生成射の語での右端保持は、具体的な頂点関数の右端保持と一致する。 -/
lemma cubeGeneratorRightKeep_concrete {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject} (g : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeGeneratorConcretePrefunctor.map
        (show _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk (X.dimension + 1) ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk (Y.dimension + 1) from
          cubeGeneratorRightKeep g) =
      concreteCubeRightKeep.map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeGeneratorConcretePrefunctor.map g) := by
  cases X
  cases Y
  cases g with
  | face b n i => exact Subtype.ext (cubeVertexRightKeep_face b _ i).symm
  | degeneracy n i => exact Subtype.ext (cubeVertexRightKeep_degeneracy _ i).symm
  | connection n i => exact Subtype.ext (cubeVertexRightKeep_connection _ i).symm

/-- 元の任意の語の右端保持は、同じ具体的な頂点写像を回収する。 -/
lemma cubeWordRightKeep_concrete {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWords} (p : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map (cubeWordRightKeep.map p) =
      concreteCubeRightKeep.map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map p) := by
  have h := cubePath_naturality (cubeWordRightKeep ⋙ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor)
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor ⋙ concreteCubeRightKeep)
    (fun X => 𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (X.dimension + 1)))
    (fun g => by
      exact Subtype.ext (congrArg Subtype.val (cubeGeneratorRightKeep_concrete g))) p
  exact Subtype.ext (congrArg Subtype.val h)

end SerrePositivity.KST.SConstruction
