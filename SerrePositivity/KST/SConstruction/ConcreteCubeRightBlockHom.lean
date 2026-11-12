module
public import SerrePositivity.KST.SConstruction.ConcreteCubeRightBlockMaps

/-! # 次元を固定した元の右ブロック作用の射
概要：元の連結積の右ブロック作用を、始域・終域の次元を明示した同じ射として与える。
方針：元の二変数関手の射をそのまま使い、恒等・合成・座標回収を保持する。
規約：対象の次元を鎖 tensor の型から逆に推測しない。使われ方：右因子自然性の評価。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 次元を固定した元の右ブロック作用の射。 -/
def concreteCubeRightBlockHom (n : ℕ) {m k : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk k) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (n + m) ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (n + k) :=
  concreteCubeTensorMap (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n)) f

/-- 次元を固定した射は元の具体的 tensor 射そのもの。 -/
lemma concreteCubeRightBlockHom_tensorMap (n : ℕ) {m k : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk k) :
    concreteCubeRightBlockHom n f = concreteCubeTensorMap (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n)) f := rfl

/-- 次元を固定した右ブロック作用は元の恒等射を保持する。 -/
lemma concreteCubeRightBlockHom_id (n m : ℕ) :
    concreteCubeRightBlockHom n (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m)) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (n + m)) :=
  concreteCubeTensorMap_id _ _

/-- 次元を固定した右ブロック作用は元の合成を保持する。 -/
lemma concreteCubeRightBlockHom_comp (n : ℕ) {m k l : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk k) (g : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk k ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk l) :
    concreteCubeRightBlockHom n (f ≫ g) =
      concreteCubeRightBlockHom n f ≫ concreteCubeRightBlockHom n g :=
  concreteCubeTensorMap_right_comp n f g

/-- 次元を固定した右ブロック作用は元の右端保持を保持する。 -/
lemma concreteCubeRightBlockHom_keep (n : ℕ) {m k : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk k) :
    concreteCubeRightBlockHom n (concreteCubeRightKeepHom f) =
      concreteCubeRightKeepHom (concreteCubeRightBlockHom n f) :=
  concreteCubeTensorMap_rightKeep n f

/-- 元の右ブロックの零面を、同じ全体の零面として回収する。 -/
lemma concreteCubeRightBlockHom_face_zero (n m : ℕ) (b : Bool) :
    concreteCubeRightBlockHom n (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace b m 0) =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace b (n + m) 0 := concreteCubeTensorMap_face_zero n m b

/-- 元の右ブロックの零削除を、同じ全体の零削除として回収する。 -/
lemma concreteCubeRightBlockHom_degeneracy_zero (n m : ℕ) :
    concreteCubeRightBlockHom n (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeDegeneracy m 0) =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeDegeneracy (n + m) 0 := concreteCubeTensorMap_degeneracy_zero n m

/-- 元の右ブロックの零 max を、同じ全体の零 max として回収する。 -/
lemma concreteCubeRightBlockHom_connection_zero (n m : ℕ) :
    concreteCubeRightBlockHom n (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeConnection m 0) =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeConnection (n + m) 0 := concreteCubeTensorMap_connection_zero n m

end SerrePositivity.KST.SConstruction
