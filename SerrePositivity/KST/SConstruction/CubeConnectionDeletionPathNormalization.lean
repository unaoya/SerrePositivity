module
public import SerrePositivity.KST.SConstruction.CubeConnectionDeletionExpression
public import SerrePositivity.KST.SConstruction.SerreCubeWordEvaluation

/-! # 元の max・削除の混合語の評価を保つ二段正規化
概要：元の path 圏の max・削除の任意の混合語を、両評価を保った二段表示へ移す。
方針：元の語と同じ式を厳密に回収し、二段正規化の評価保存を適用する。
規約：二段表示の一意性と面を含む一般の語は別工程。
使われ方：三段表示へ向かう混合語の正規化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded

/-- max・削除の混合式を元の生成語の path として厳密に実現する。 -/
def cubeConnectionDeletionExpressionPath {n : ℕ} :
    {m : ℕ} → CubeConnectionDeletionExpression n m →
      Quiver.Path (CubeWordObject.mk n) (CubeWordObject.mk m)
  | _, .id _ => .nil
  | _, .connect p i =>
      (cubeConnectionDeletionExpressionPath p).cons (CubeGenerator.connection _ i)
  | _, .erase p i => (cubeConnectionDeletionExpressionPath p).cons (CubeGenerator.degeneracy _ i)
termination_by structural _m p => p

/-- 混合式の path の具体的評価は、同じ式の元の頂点関数。 -/
lemma cubeConnectionDeletionExpressionPath_concrete {n m : ℕ}
    (p : CubeConnectionDeletionExpression n m) :
    (cubeWordConcreteFunctor.map (cubeConnectionDeletionExpressionPath p)).val =
      cubeConnectionDeletionExpressionVertex p := by
  induction p with
  | id => rfl
  | connect p i ih =>
    change cubeVertexConnection _ i ∘
      (cubeWordConcreteFunctor.map (cubeConnectionDeletionExpressionPath p)).val =
        cubeVertexConnection _ i ∘ cubeConnectionDeletionExpressionVertex p
    rw [ih]
    rfl
  | erase p i ih =>
    change cubeVertexDegeneracy _ i ∘
      (cubeWordConcreteFunctor.map (cubeConnectionDeletionExpressionPath p)).val =
        cubeVertexDegeneracy _ i ∘ cubeConnectionDeletionExpressionVertex p
    rw [ih]
    rfl

/-- 混合式の path の Serre 評価は、同じ式の元の Serre 射。 -/
lemma cubeConnectionDeletionExpressionPath_serre (A : Type u) [CommRing A] {n m : ℕ}
    (p : CubeConnectionDeletionExpression n m) :
    (serreCubeWordFunctor A).map (cubeConnectionDeletionExpressionPath p) =
      serreCubeConnectionDeletionExpression A p := by
  induction p with
  | id => rfl
  | connect p i ih =>
    change (serreCubeWordFunctor A).map (cubeConnectionDeletionExpressionPath p) ≫
      serreCubeConnection A _ i =
        serreCubeConnectionDeletionExpression A p ≫ serreCubeConnection A _ i
    rw [ih]
    rfl
  | erase p i ih =>
    change (serreCubeWordFunctor A).map (cubeConnectionDeletionExpressionPath p) ≫
      serreCubeDegeneracy A _ i =
        serreCubeConnectionDeletionExpression A p ≫ serreCubeDegeneracy A _ i
    rw [ih]
    rfl

/-- 元の語が max と削除だけからなる条件。 -/
inductive CubeConnectionDeletionPath : {X Y : CubeWordObject} → Quiver.Path X Y → Prop
  | nil (X : CubeWordObject) : CubeConnectionDeletionPath (.nil : Quiver.Path X X)
  | connect {X : CubeWordObject} {m : ℕ}
      (p : Quiver.Path X (CubeWordObject.mk (m + 2))) (hp : CubeConnectionDeletionPath p)
      (i : Fin (m + 1)) : CubeConnectionDeletionPath
        (p.cons (show CubeWordObject.mk (m + 2) ⟶ CubeWordObject.mk (m + 1) from
          CubeGenerator.connection m i))
  | erase {X : CubeWordObject} {m : ℕ} (p : Quiver.Path X (CubeWordObject.mk (m + 1)))
      (hp : CubeConnectionDeletionPath p) (i : Fin (m + 1)) : CubeConnectionDeletionPath
        (p.cons (show CubeWordObject.mk (m + 1) ⟶ CubeWordObject.mk m from
          CubeGenerator.degeneracy m i))

/-- 元の max・削除の混合語は、その同じ構文の式から厳密に回収される。 -/
lemma cubeConnectionDeletionPath_exists_expression {X Y : CubeWordObject} {p : Quiver.Path X Y}
    (h : CubeConnectionDeletionPath p) :
    ∃ e : CubeConnectionDeletionExpression X.dimension Y.dimension,
      cubeConnectionDeletionExpressionPath e = p := by
  induction h with
  | nil => exact ⟨.id X.dimension, rfl⟩
  | connect p hp i ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨.connect e i, ?_⟩
    change (cubeConnectionDeletionExpressionPath e).cons _ = p.cons _
    rw [he]
  | erase p hp i ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨.erase e i, ?_⟩
    change (cubeConnectionDeletionExpressionPath e).cons _ = p.cons _
    rw [he]

/-- 元の max・削除の任意の混合語を、両方の実際の評価を保った二段表示へ移す。 -/
lemma cubeConnectionDeletionPath_normalization (A : Type u) [CommRing A]
    {X Y : CubeWords} (p : X ⟶ Y) (hp : CubeConnectionDeletionPath p) :
    ∃ r : CubeDeletionConnectionNormal X.dimension Y.dimension,
      cubeDeletionConnectionNormalVertex r = (cubeWordConcreteFunctor.map p).val ∧
        serreCubeDeletionConnectionNormal A r = (serreCubeWordFunctor A).map p := by
  obtain ⟨e, he⟩ := cubeConnectionDeletionPath_exists_expression hp
  have hvertex := cubeConnectionDeletionExpressionPath_concrete e
  have hserre := cubeConnectionDeletionExpressionPath_serre A e
  erw [he] at hvertex hserre
  exact ⟨cubeConnectionDeletionExpressionNormal e,
    (cubeConnectionDeletionExpressionNormal_vertex e).trans hvertex.symm,
    (serreCubeConnectionDeletionExpressionNormal A e).trans hserre.symm⟩

end SerrePositivity.KST.SConstruction
