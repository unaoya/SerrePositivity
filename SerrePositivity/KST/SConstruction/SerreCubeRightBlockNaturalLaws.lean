module
public import SerrePositivity.KST.SConstruction.SerreCubeRightBlockNatural

/-! # 右ブロック自然性の恒等・合成と零座標
概要：元の右ブロックの可換条件は恒等・合成を保ち、元の全零座標生成射で成り立つ。
方針：同じ具体的 tensor 関手と同じ鎖射の法則を使う。
規約：生成射の条件を新たな仮定に置かない。使われ方：全生成語の右因子自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の右ブロックの恒等射について連結比較は自然。 -/
lemma serreCubeRightBlockNatural_id (n m : ℕ) :
    SerreCubeRightBlockNatural A n (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m)) := by
  dsimp only [SerreCubeRightBlockNatural]
  erw [concreteCubeRightBlockHom_id, serreConcreteCubeMap_id A,
    serreConcreteCubeMap_id A, serreCubeTensorHom_id]
  erw [Category.id_comp]

/-- 元の二つの右ブロックの自然性は、その元の合成でも成り立つ。 -/
lemma serreCubeRightBlockNatural_comp (n : ℕ) {m k l : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk k) (g : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk k ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk l)
    (hf : SerreCubeRightBlockNatural A n f) (hg : SerreCubeRightBlockNatural A n g) :
    SerreCubeRightBlockNatural A n (f ≫ g) := by
  dsimp only [SerreCubeRightBlockNatural] at hf hg ⊢
  erw [concreteCubeRightBlockHom_comp, serreConcreteCubeMap_comp A,
    serreConcreteCubeMap_comp A, Category.assoc, hg, ← Category.assoc, hf,
    Category.assoc]
  rw [← serreCubeTensorHom_comp A (𝟙 (serreCubeComonoid A n))
    (𝟙 (serreCubeComonoid A n)) (serreConcreteCubeMap A f)
    (serreConcreteCubeMap A g), Category.id_comp]

/-- 元の右ブロックの零面について連結比較は自然。 -/
lemma serreCubeRightBlockNatural_face_zero (n m : ℕ) (b : Bool) :
    SerreCubeRightBlockNatural A n (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace b m 0) := by
  dsimp only [SerreCubeRightBlockNatural]
  erw [concreteCubeRightBlockHom_face_zero, serreConcreteCubeMap_face A b (n + m) 0,
    serreConcreteCubeMap_face A b m 0]
  exact serreCubeTensor_rightFace_zero A n m b

/-- 元の右ブロックの零削除について連結比較は自然。 -/
lemma serreCubeRightBlockNatural_degeneracy_zero (n m : ℕ) :
    SerreCubeRightBlockNatural A n (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeDegeneracy m 0) := by
  dsimp only [SerreCubeRightBlockNatural]
  erw [concreteCubeRightBlockHom_degeneracy_zero, serreConcreteCubeMap_degeneracy A (n + m) 0,
    serreConcreteCubeMap_degeneracy A m 0]
  exact serreCubeTensor_rightDegeneracy_zero A n m

/-- 元の右ブロックの零 max について連結比較は自然。 -/
lemma serreCubeRightBlockNatural_connection_zero (n m : ℕ) :
    SerreCubeRightBlockNatural A n (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeConnection m 0) := by
  have hb : serreConcreteCubeMap A
      (concreteCubeRightBlockHom n (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeConnection m 0)) =
        serreCubeConnection A (n + m) 0 := by
    rw [concreteCubeRightBlockHom_connection_zero n m]
    exact serreConcreteCubeMap_connection A (n + m) 0
  exact serreCubeRightBlockNatural_of_evaluations A n (m := m + 2) (k := m + 1)
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeConnection m 0) (serreCubeConnection A (n + m) 0) (serreCubeConnection A m 0)
    hb (serreConcreteCubeMap_connection A m 0) (serreCubeTensor_rightConnection_zero A n m)

end SerrePositivity.KST.SConstruction
