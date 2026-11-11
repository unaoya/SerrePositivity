module
public import SerrePositivity.KST.SConstruction.CubeFaceDeletionExpression
public import SerrePositivity.KST.SConstruction.SerreCubeWordEvaluation

/-! # 元の面・削除の混合語の評価を保つ二段正規化
概要：元の path 圏の面・削除の任意の混合語を、二つの評価を保った二段表示へ移す。
方針：元の語と同じ式を厳密に回収し、二段正規化の評価保存を適用する。
規約：二段表示の一意性と connection を含む一般の語は別工程。
使われ方：三段表示へ向かう混合語の正規化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded

/-- 面・削除の混合式を元の生成語の path として厳密に実現する。 -/
def cubeFaceDeletionExpressionPath {n : ℕ} : {m : ℕ} → CubeFaceDeletionExpression n m →
    Quiver.Path (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk n) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk m)
  | _, .id _ => .nil
  | _, .point p b i => (cubeFaceDeletionExpressionPath p).cons (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeGenerator.face b _ i)
  | _, .erase p i => (cubeFaceDeletionExpressionPath p).cons (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeGenerator.degeneracy _ i)
termination_by structural _m p => p

/-- 混合式の path の具体的評価は、同じ式の元の頂点関数。 -/
lemma cubeFaceDeletionExpressionPath_concrete {n m : ℕ} (p : CubeFaceDeletionExpression n m) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map (cubeFaceDeletionExpressionPath p)).val =
      cubeFaceDeletionExpressionVertex p := by
  induction p with
  | id => rfl
  | point p b i ih =>
    change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b _ i ∘
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map (cubeFaceDeletionExpressionPath p)).val =
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b _ i ∘ cubeFaceDeletionExpressionVertex p
    rw [ih]
    rfl
  | erase p i ih =>
    change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy _ i ∘
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map (cubeFaceDeletionExpressionPath p)).val =
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy _ i ∘ cubeFaceDeletionExpressionVertex p
    rw [ih]
    rfl

/-- 混合式の path の Serre 評価は、同じ式の元の Serre 射。 -/
lemma cubeFaceDeletionExpressionPath_serre (A : Type u) [CommRing A] {n m : ℕ}
    (p : CubeFaceDeletionExpression n m) :
    (serreCubeWordFunctor A).map (cubeFaceDeletionExpressionPath p) =
      serreCubeFaceDeletionExpression A p := by
  induction p with
  | id => rfl
  | point p b i ih =>
    change (serreCubeWordFunctor A).map (cubeFaceDeletionExpressionPath p) ≫
      serreCubeFace A b _ i = serreCubeFaceDeletionExpression A p ≫ serreCubeFace A b _ i
    rw [ih]
    rfl
  | erase p i ih =>
    change (serreCubeWordFunctor A).map (cubeFaceDeletionExpressionPath p) ≫
      serreCubeDegeneracy A _ i = serreCubeFaceDeletionExpression A p ≫ serreCubeDegeneracy A _ i
    rw [ih]
    rfl

/-- 元の語が面と削除だけからなる条件。 -/
inductive CubeFaceDeletionPath : {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject} → Quiver.Path X Y → Prop
  | nil (X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject) : CubeFaceDeletionPath (.nil : Quiver.Path X X)
  | point {X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject} {m : ℕ} (p : Quiver.Path X (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk m))
      (hp : CubeFaceDeletionPath p) (b : Bool) (i : Fin (m + 1)) : CubeFaceDeletionPath
        (p.cons (show _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk m ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk (m + 1) from
          _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeGenerator.face b m i))
  | erase {X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject} {m : ℕ} (p : Quiver.Path X (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk (m + 1)))
      (hp : CubeFaceDeletionPath p) (i : Fin (m + 1)) : CubeFaceDeletionPath
        (p.cons (show _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk (m + 1) ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk m from
          _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeGenerator.degeneracy m i))

/-- 元の面・削除の混合語は、その同じ構文の式から厳密に回収される。 -/
lemma cubeFaceDeletionPath_exists_expression {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject} {p : Quiver.Path X Y}
    (h : CubeFaceDeletionPath p) : ∃ e : CubeFaceDeletionExpression X.dimension Y.dimension,
      cubeFaceDeletionExpressionPath e = p := by
  induction h with
  | nil => exact ⟨.id X.dimension, rfl⟩
  | point p hp b i ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨.point e b i, ?_⟩
    change (cubeFaceDeletionExpressionPath e).cons _ = p.cons _
    rw [he]
  | erase p hp i ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨.erase e i, ?_⟩
    change (cubeFaceDeletionExpressionPath e).cons _ = p.cons _
    rw [he]

/-- 元の面・削除の任意の混合語を、両方の実際の評価を保った二段表示へ移す。 -/
lemma cubeFaceDeletionPath_normalization (A : Type u) [CommRing A]
    {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWords} (p : X ⟶ Y) (hp : CubeFaceDeletionPath p) :
    ∃ r : CubeDeletionFaceNormal X.dimension Y.dimension,
      cubeDeletionFaceNormalVertex r = (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map p).val ∧
        serreCubeDeletionFaceNormal A r = (serreCubeWordFunctor A).map p := by
  obtain ⟨e, he⟩ := cubeFaceDeletionPath_exists_expression hp
  have hvertex := cubeFaceDeletionExpressionPath_concrete e
  have hserre := cubeFaceDeletionExpressionPath_serre A e
  erw [he] at hvertex hserre
  exact ⟨cubeFaceDeletionExpressionNormal e,
    (cubeFaceDeletionExpressionNormal_vertex e).trans hvertex.symm,
    (serreCubeFaceDeletionExpressionNormal A e).trans hserre.symm⟩

end SerrePositivity.KST.SConstruction
