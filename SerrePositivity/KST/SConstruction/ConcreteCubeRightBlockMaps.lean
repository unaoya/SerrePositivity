module
public import SerrePositivity.KST.SConstruction.ConcreteCubeTensor
public import SerrePositivity.KST.SConstruction.CubeRightKeepHom

/-! # 元の連結積の右ブロックの生成操作
概要：左ブロックを固定した連結積が、元の零座標操作と右端保持を回収する。
方針：全連結頂点で元の座標関数を照合する。
規約：右ブロックを先に数える元の規約を保つ。使われ方：鎖比較の右因子自然性。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 左を固定した連結積の右ブロックの零面は、元の全体の零面。 -/
lemma concreteCubeTensorMap_face_zero (n m : ℕ) (b : Bool) :
    concreteCubeTensorMap (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n)) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace b m 0) =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace b (n + m) 0 := by
  apply Subtype.ext
  exact (cubeVertexTensor_eq_of_join _root_.id (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b m 0)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b (n + m) 0) (by
      intro x y
      simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace, Fin.insertNth_zero', cubeVertexJoin, id_eq,
        Fin.cons_zero, Fin.cons_succ])).symm

/-- 左を固定した連結積の右ブロックの零削除は、元の全体の零削除。 -/
lemma concreteCubeTensorMap_degeneracy_zero (n m : ℕ) :
    concreteCubeTensorMap (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n)) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeDegeneracy m 0) =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeDegeneracy (n + m) 0 := by
  apply Subtype.ext
  exact (cubeVertexTensor_eq_of_join _root_.id (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy m 0)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy (n + m) 0) (by
      intro x y
      rfl)).symm

/-- 左を固定した連結積の右ブロックの零 max は、元の全体の零 max。 -/
lemma concreteCubeTensorMap_connection_zero (n m : ℕ) :
    concreteCubeTensorMap (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n)) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeConnection m 0) =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeConnection (n + m) 0 := by
  apply Subtype.ext
  exact (cubeVertexTensor_eq_of_join _root_.id (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection m 0)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection (n + m) 0) (by
      intro x y
      have h := cubeVertexJoin_connection_zero x (fun j => y j.succ) (y 0)
      change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection (n + m) 0
          (cubeVertexJoin (n := n) (m := m + 2) x (Fin.cons (y 0) (fun j => y j.succ))) =
        cubeVertexJoin (n := n) (m := m + 1) x
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection m 0 (Fin.cons (y 0) (fun j => y j.succ))) at h
      have hy : Fin.cons (y 0) (fun j => y j.succ) = y := Fin.cons_self_tail y
      rw [hy] at h
      exact h)).symm

/-- 左を固定した連結積は、元の右端保持と厳密に可換。 -/
lemma concreteCubeTensorMap_rightKeep (n : ℕ) {m k : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk k) :
    concreteCubeTensorMap (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n)) (concreteCubeRightKeepHom f) =
      concreteCubeRightKeepHom (concreteCubeTensorMap (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n)) f) :=
  Subtype.ext rfl

/-- 左を固定した元の連結積は、右ブロックの元の合成を保つ。 -/
lemma concreteCubeTensorMap_right_comp (n : ℕ) {X Y Z : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    concreteCubeTensorMap (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n)) (f ≫ g) =
      concreteCubeTensorMap (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n)) f ≫
        concreteCubeTensorMap (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n)) g := by
  simpa only [Category.id_comp] using
    concreteCubeTensorMap_comp (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n)) (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n)) f g

/-- 元の両因子の連結射は、左因子と右因子の元の二作用の合成。 -/
lemma concreteCubeTensorMap_factor {X X' Y Y' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ X') (g : Y ⟶ Y') :
    concreteCubeTensorMap f g =
      concreteCubeTensorMap f (𝟙 Y) ≫ concreteCubeTensorMap (𝟙 X') g := by
  simpa only [Category.comp_id, Category.id_comp] using
    concreteCubeTensorMap_comp f (𝟙 X') (𝟙 Y) g

end SerrePositivity.KST.SConstruction
