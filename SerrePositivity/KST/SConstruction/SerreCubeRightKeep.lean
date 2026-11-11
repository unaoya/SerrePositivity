module
public import SerrePositivity.KST.SConstruction.CubePathNaturality

/-! # 右端保持した元の生成射の Serre 評価
概要：元の具体的立方体の生成射に右端保持を加えると、座標をずらした元の Serre 射を回収する。
方針：各生成射の具体的評価と、元の Serre 関手の回収式を合成する。
規約：interval は右因子のまま。使われ方：任意次元の鎖立方体の tensor 比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の face の右端保持は、座標を一つずらした元の Serre 射を回収する。 -/
lemma serreConcreteCubeRightKeep_face (b : Bool) (n : ℕ) (i : Fin (n + 1)) :
    (serreConcreteCubeFunctor A).map (concreteCubeRightKeep.map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace b n i)) =
      serreCubeFace A b (n + 1) i.succ := by
  have h : concreteCubeRightKeep.map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace b n i) =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace b (n + 1) i.succ := Subtype.ext (cubeVertexRightKeep_face b n i)
  exact (congrArg (fun k => (serreConcreteCubeFunctor A).map k) h).trans
    (serreConcreteCubeFunctor_face A b (n + 1) i.succ)

/-- 元の degeneracy の右端保持は、座標を一つずらした元の Serre 射を回収する。 -/
lemma serreConcreteCubeRightKeep_degeneracy (n : ℕ) (i : Fin (n + 1)) :
    (serreConcreteCubeFunctor A).map (concreteCubeRightKeep.map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeDegeneracy n i)) =
      serreCubeDegeneracy A (n + 1) i.succ := by
  have h : concreteCubeRightKeep.map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeDegeneracy n i) =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeDegeneracy (n + 1) i.succ := Subtype.ext (cubeVertexRightKeep_degeneracy n i)
  exact (congrArg (fun k => (serreConcreteCubeFunctor A).map k) h).trans
    (serreConcreteCubeFunctor_degeneracy A (n + 1) i.succ)

/-- 元の connection の右端保持は、座標を一つずらした元の Serre 射を回収する。 -/
lemma serreConcreteCubeRightKeep_connection (n : ℕ) (i : Fin (n + 1)) :
    (serreConcreteCubeFunctor A).map (concreteCubeRightKeep.map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeConnection n i)) =
      serreCubeConnection A (n + 1) i.succ := by
  have h : concreteCubeRightKeep.map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeConnection n i) =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeConnection (n + 1) i.succ := Subtype.ext (cubeVertexRightKeep_connection n i)
  exact (congrArg (fun k => (serreConcreteCubeFunctor A).map k) h).trans
    (serreConcreteCubeFunctor_connection A (n + 1) i.succ)

end SerrePositivity.KST.SConstruction
