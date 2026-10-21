module
public import SerrePositivity.KST.SConstruction.SerreRightKeepHomTensor

/-! # 元の全具体的射の右端保持と鎖 tensor
概要：元の任意の具体的立方体の射で、右端保持の Serre 評価が元の右 tensor と一致する。
方針：型を固定した恒等・合成保存を使い、元の生成条件で帰納する。
規約：元の射と同じ BF 入力への作用を保持する。使われ方：有限 tensor 比較の自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の全生成写像で、右端保持の評価は元の右 tensor を厳密に回収する。 -/
lemma serreCubeRightKeep_generated {n m : ℕ} {f : CubeVertex n → CubeVertex m}
    (h : CubeMapGenerated f) :
    (serreConcreteCubeFunctor A).map (concreteCubeRightKeepHom ⟨f, h⟩) =
      serreCubeRightTensorMap A (n := n) (m := m)
        ((serreConcreteCubeFunctor A).map ⟨f, h⟩) := by
  induction h with
  | id n =>
    change (serreConcreteCubeFunctor A).map (concreteCubeRightKeepHom (𝟙 (ConcreteCube.mk n))) =
      serreCubeRightTensorMap A (n := n) (m := n)
        ((serreConcreteCubeFunctor A).map (𝟙 (ConcreteCube.mk n)))
    erw [concreteCubeRightKeepHom_id, (serreConcreteCubeFunctor A).map_id,
      (serreConcreteCubeFunctor A).map_id]
    exact (serreCubeRightTensorMap_id A n).symm
  | face b n i =>
    change (serreConcreteCubeFunctor A).map (concreteCubeRightKeepHom (concreteCubeFace b n i)) =
      serreCubeRightTensorMap A (n := n) (m := n + 1)
        ((serreConcreteCubeFunctor A).map (concreteCubeFace b n i))
    rw [serreConcreteCubeFunctor_face]
    exact serreRightKeepHomTensor_face A b n i
  | degeneracy n i =>
    change (serreConcreteCubeFunctor A).map (concreteCubeRightKeepHom
      (concreteCubeDegeneracy n i)) =
      serreCubeRightTensorMap A (n := n + 1) (m := n)
        ((serreConcreteCubeFunctor A).map (concreteCubeDegeneracy n i))
    rw [serreConcreteCubeFunctor_degeneracy]
    exact serreRightKeepHomTensor_degeneracy A n i
  | connection n i =>
    change (serreConcreteCubeFunctor A).map (concreteCubeRightKeepHom
      (concreteCubeConnection n i)) =
      serreCubeRightTensorMap A (n := n + 2) (m := n + 1)
        ((serreConcreteCubeFunctor A).map (concreteCubeConnection n i))
    rw [serreConcreteCubeFunctor_connection]
    exact serreRightKeepHomTensor_connection A n i
  | @comp n m l f g hf hg ihf ihg =>
    change (serreConcreteCubeFunctor A).map (concreteCubeRightKeepHom
      ((⟨f, hf⟩ : ConcreteCube.mk n ⟶ ConcreteCube.mk m) ≫
        (⟨g, hg⟩ : ConcreteCube.mk m ⟶ ConcreteCube.mk l))) =
      serreCubeRightTensorMap A (n := n) (m := l)
        ((serreConcreteCubeFunctor A).map (⟨f, hf⟩ ≫ ⟨g, hg⟩))
    erw [concreteCubeRightKeepHom_comp, (serreConcreteCubeFunctor A).map_comp,
      (serreConcreteCubeFunctor A).map_comp, ihf, ihg]
    exact (serreCubeRightTensorMap_comp A (n := n) (m := m) (l := l)
      ((serreConcreteCubeFunctor A).map ⟨f, hf⟩)
      ((serreConcreteCubeFunctor A).map ⟨g, hg⟩)).symm

/-- 元の任意の具体的立方体の射で、同じ右 tensor を厳密に回収する。 -/
lemma serreConcreteCubeRightKeep_tensor {n m : ℕ}
    (f : ConcreteCube.mk n ⟶ ConcreteCube.mk m) :
    (serreConcreteCubeFunctor A).map (concreteCubeRightKeepHom f) =
      serreCubeRightTensorMap A (n := n) (m := m) ((serreConcreteCubeFunctor A).map f) :=
  serreCubeRightKeep_generated A f.property

/-- 元の右端保持関手の全射は、同じ次元を持つ元の右 tensor を回収する。 -/
lemma serreConcreteCubeRightKeep_tensor_map {X Y : ConcreteCube} (f : X ⟶ Y) :
    (serreConcreteCubeFunctor A).map (concreteCubeRightKeep.map f) =
      serreCubeRightTensorMap A (n := X.dimension) (m := Y.dimension)
        ((serreConcreteCubeFunctor A).map f) := by
  cases X
  cases Y
  exact serreConcreteCubeRightKeep_tensor A f

end SerrePositivity.KST.SConstruction
