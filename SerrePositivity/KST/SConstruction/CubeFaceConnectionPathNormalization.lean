module
public import SerrePositivity.KST.SConstruction.CubeThreeNormal

/-! # 元の面の語の後の一 connection の三段正規化
概要：元の path 圏の任意の面の語と一 connection を、両評価を保つ三段表示へ移す。
方針：元の面の式を厳密に回収し、標準化と面の後の connection の評価保存を合成する。
規約：全混合語の帰納と三段表示の一意性は別工程。使われ方：一般の Serre 語評価の降下。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded

/-- 元の面の語の後の一 connection を、元の両評価を保った三段表示へ移す。 -/
lemma cubeFacePath_connection_normalization (A : Type u) [CommRing A]
    {X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject} {m : ℕ} (p : Quiver.Path X (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk (m + 2)))
    (hp : CubeFacePath p) (i : Fin (m + 1)) :
    ∃ r : CubeThreeNormal X.dimension (m + 1),
      cubeThreeNormalVertex r =
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map
          (p.cons (show _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk (m + 2) ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk (m + 1) from
            _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeGenerator.connection m i))).val ∧
      serreCubeThreeNormal A r = (serreCubeWordFunctor A).map
        (p.cons (show _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk (m + 2) ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk (m + 1) from
          _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeGenerator.connection m i)) := by
  obtain ⟨e, he⟩ := cubeFacePath_exists_expression hp
  have hvertex := cubeFaceExpressionPath_concrete e
  have hserre := cubeFaceExpressionPath_serre A e
  erw [he] at hvertex hserre
  have hv : cubeFaceNormalVertex (cubeFaceExpressionNormal e) =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map p).val :=
    (cubeFaceExpressionNormal_vertex e).trans hvertex.symm
  have hs : serreCubeFaceNormal A (cubeFaceExpressionNormal e) =
      (serreCubeWordFunctor A).map p :=
    (serreCubeFaceExpressionNormal A e).trans hserre.symm
  obtain ⟨r, hr, hsr⟩ := cubeFaceNormal_connection_three A (cubeFaceExpressionNormal e) i
  refine ⟨r, ?_, ?_⟩
  · change cubeThreeNormalVertex r =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection m i ∘ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map p).val
    rw [hv] at hr
    exact hr
  · change serreCubeThreeNormal A r =
      (serreCubeWordFunctor A).map p ≫ serreCubeConnection A m i
    rw [hs] at hsr
    exact hsr

end SerrePositivity.KST.SConstruction
