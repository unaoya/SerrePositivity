module
public import SerrePositivity.KST.SConstruction.SerreConcreteCubeFunctor

/-! # 次元を固定した元の具体的 Serre 射
概要：元の関手の射を、始域・終域の鎖立方体の次元を明示して回収する。
方針：同じ関手の射を使い、元の恒等・合成・三生成射を保持する。
規約：関手の対象の型から tensor 因子を逆に推測しない。使われ方：連結鎖比較の評価。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 始域・終域を固定した、元の具体的 Serre 射。 -/
def serreConcreteCubeMap {n m : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m) :
    serreCubeComonoid A n ⟶ serreCubeComonoid A m := (serreConcreteCubeFunctor A).map f

/-- 次元を固定した射は、元の関手の射そのもの。 -/
lemma serreConcreteCubeMap_map {n m : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m) :
    serreConcreteCubeMap A f = (serreConcreteCubeFunctor A).map f := rfl

/-- 次元を固定した Serre 射は元の恒等射を保持する。 -/
lemma serreConcreteCubeMap_id (n : ℕ) :
    serreConcreteCubeMap A (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n)) = 𝟙 (serreCubeComonoid A n) :=
  (serreConcreteCubeFunctor A).map_id _

/-- 次元を固定した Serre 射は元の合成を保持する。 -/
lemma serreConcreteCubeMap_comp {n m k : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m)
    (g : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk k) :
    serreConcreteCubeMap A (f ≫ g) = serreConcreteCubeMap A f ≫ serreConcreteCubeMap A g :=
  (serreConcreteCubeFunctor A).map_comp _ _

/-- 元の面は、同じ座標の元の鎖の面を回収する。 -/
lemma serreConcreteCubeMap_face (b : Bool) (n : ℕ) (i : Fin (n + 1)) :
    serreConcreteCubeMap A (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace b n i) = serreCubeFace A b n i :=
  serreConcreteCubeFunctor_face A b n i

/-- 元の削除は、同じ座標の元の鎖の削除を回収する。 -/
lemma serreConcreteCubeMap_degeneracy (n : ℕ) (i : Fin (n + 1)) :
    serreConcreteCubeMap A (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeDegeneracy n i) = serreCubeDegeneracy A n i :=
  serreConcreteCubeFunctor_degeneracy A n i

/-- 元の max は、同じ座標の元の鎖の max を回収する。 -/
lemma serreConcreteCubeMap_connection (n : ℕ) (i : Fin (n + 1)) :
    serreConcreteCubeMap A (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeConnection n i) = serreCubeConnection A n i :=
  serreConcreteCubeFunctor_connection A n i

end SerrePositivity.KST.SConstruction
