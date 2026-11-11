module
public import SerrePositivity.KST.SConstruction.SerreCubeRightTensorMap

/-! # 次元を明示した右端保持と元の鎖 tensor
概要：元の三生成射の右端保持を、源・標的の次元を保ったまま右 tensor と照合する。
方針：具体的な射の等号と、元の全座標の再帰式を合成する。
規約：区間は右因子。使われ方：全具体射の鎖 tensor 比較の自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 次元を明示した元の面の右端保持は、同じ面の右 tensor。 -/
lemma serreRightKeepHomTensor_face (b : Bool) (n : ℕ) (i : Fin (n + 1)) :
    (serreConcreteCubeFunctor A).map (concreteCubeRightKeepHom (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace b n i)) =
      serreCubeRightTensorMap A (n := n) (m := n + 1) (serreCubeFace A b n i) := by
  have h0 := (congrArg (fun k => (serreConcreteCubeFunctor A).map k)
    (concreteCubeRightKeepHom_face b n i)).trans
      (serreConcreteCubeFunctor_face A b (n + 1) i.succ)
  exact h0.trans (serreCubeRightTensorMap_face A b n i)

/-- 次元を明示した元の削除の右端保持は、同じ削除の右 tensor。 -/
lemma serreRightKeepHomTensor_degeneracy (n : ℕ) (i : Fin (n + 1)) :
    (serreConcreteCubeFunctor A).map (concreteCubeRightKeepHom (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeDegeneracy n i)) =
      serreCubeRightTensorMap A (n := n + 1) (m := n) (serreCubeDegeneracy A n i) := by
  have h0 := (congrArg (fun k => (serreConcreteCubeFunctor A).map k)
    (concreteCubeRightKeepHom_degeneracy n i)).trans
      (serreConcreteCubeFunctor_degeneracy A (n + 1) i.succ)
  exact h0.trans (serreCubeRightTensorMap_degeneracy A n i)

/-- 次元を明示した元の connection の右端保持は、同じ connection の右 tensor。 -/
lemma serreRightKeepHomTensor_connection (n : ℕ) (i : Fin (n + 1)) :
    (serreConcreteCubeFunctor A).map (concreteCubeRightKeepHom (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeConnection n i)) =
      serreCubeRightTensorMap A (n := n + 2) (m := n + 1) (serreCubeConnection A n i) := by
  have h0 := (congrArg (fun k => (serreConcreteCubeFunctor A).map k)
    (concreteCubeRightKeepHom_connection n i)).trans
      (serreConcreteCubeFunctor_connection A (n + 1) i.succ)
  exact h0.trans (serreCubeRightTensorMap_connection A n i)

end SerrePositivity.KST.SConstruction
