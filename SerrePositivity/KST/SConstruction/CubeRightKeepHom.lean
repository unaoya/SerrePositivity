module
public import SerrePositivity.KST.SConstruction.CubeRightKeep

/-! # 次元を明示した右端保持の射
概要：元の右端保持関手と同じ射を、源と標的の立方体の次元を明示して与える。
方針：同じ生成関数と生成条件をそのまま束ねる。
規約：元の関手との一致は射そのものの等号。使われ方：鎖 tensor 比較での対象型の固定。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の右端保持の射を、源と標的の次元を明示して束ねる。 -/
def concreteCubeRightKeepHom {n m : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (n + 1) ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (m + 1) :=
  ⟨cubeVertexRightKeep f.val, cubeMapGenerated_rightKeep f.property⟩

/-- 次元を明示した射は、元の右端保持関手の射そのもの。 -/
lemma concreteCubeRightKeepHom_map {n m : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m) :
    concreteCubeRightKeepHom f = concreteCubeRightKeep.map f := rfl

/-- 次元を明示した右端保持は、元の恒等射を保つ。 -/
lemma concreteCubeRightKeepHom_id (n : ℕ) :
    concreteCubeRightKeepHom (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n)) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (n + 1)) :=
  Subtype.ext (cubeVertexRightKeep_id n)

/-- 次元を明示した右端保持は、元の射の合成を保つ。 -/
lemma concreteCubeRightKeepHom_comp {n m l : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m) (g : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk l) :
    concreteCubeRightKeepHom (f ≫ g) =
      concreteCubeRightKeepHom f ≫ concreteCubeRightKeepHom g :=
  Subtype.ext (cubeVertexRightKeep_comp f.val g.val)

/-- 次元を明示した面の右端保持は、元の一つ内側の面。 -/
lemma concreteCubeRightKeepHom_face (b : Bool) (n : ℕ) (i : Fin (n + 1)) :
    concreteCubeRightKeepHom (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace b n i) =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace b (n + 1) i.succ := Subtype.ext (cubeVertexRightKeep_face b n i)

/-- 次元を明示した削除の右端保持は、元の一つ内側の削除。 -/
lemma concreteCubeRightKeepHom_degeneracy (n : ℕ) (i : Fin (n + 1)) :
    concreteCubeRightKeepHom (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeDegeneracy n i) =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeDegeneracy (n + 1) i.succ := Subtype.ext (cubeVertexRightKeep_degeneracy n i)

/-- 次元を明示した connection の右端保持は、元の一つ内側の connection。 -/
lemma concreteCubeRightKeepHom_connection (n : ℕ) (i : Fin (n + 1)) :
    concreteCubeRightKeepHom (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeConnection n i) =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeConnection (n + 1) i.succ := Subtype.ext (cubeVertexRightKeep_connection n i)

end SerrePositivity.KST.SConstruction
