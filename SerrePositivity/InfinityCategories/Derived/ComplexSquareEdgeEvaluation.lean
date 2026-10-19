module
public import SerrePositivity.InfinityCategories.Derived.ComplexSquarePostcomposeEdge
public import SerrePositivity.InfinityCategories.Derived.ComplexSquarePrecomposeEdge
public import SerrePositivity.InfinityCategories.Stable.SliceSquareDiagramFixed
public import SerrePositivity.InfinityCategories.Stable.ColimitSquareComparison

/-! # 前合成・後合成の四角形比較辺の端点成分

概要：四角形全体の辺を始点・終点で評価し、指定した鎖写像または定値辺へ同定する。
方針：slice/coslice の図式表示の評価式と、実際の辺の射影の式を使う。
規約：端点の表示変更に依存しない一単体の等式。使われ方：D7 の suspension の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.ComplexSquareData
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {S : Type u} [CommRing S] {V A B C D E : Complex S}
variable (s : ComplexSquareData A B C D)

/-- 終点を後合成する四角形比較の終点成分は指定射 q。 -/
lemma postcomposeSquareEdge_target (q : D ⟶ E) :
    ((s.postcomposeSquareEdge q).map ((truncation 2).map
      (evaluateFunctorAt (Y := dgNerve S (Complex S))
        (squareVertex (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])) 1 1)))).edge =
      (complexEdge q).edge := by
  change (cosliceSquareDiagramMap (pushoutSpan s.square) ≫
    evaluateFunctorAt (Y := dgNerve S (Complex S))
      (squareVertex (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])) 1 1)).app _
        (s.postcomposeSliceEdge q).edge = _
  rw [cosliceSquareDiagramMap_targetEvaluation]
  exact s.postcomposeSliceEdge_projection q

/-- 終点を後合成する四角形比較の始点成分は定値辺。 -/
lemma postcomposeSquareEdge_source (q : D ⟶ E) :
    ((s.postcomposeSquareEdge q).map ((truncation 2).map
      (evaluateFunctorAt (Y := dgNerve S (Complex S))
        (squareVertex (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])) 0 0)))).edge =
      PinchedHom.constant ((spanSourceEvaluation (dgNerve S (Complex S))).app (Opposite.op ⦋0⦌)
        (functorVertex (pushoutSpan s.square))) 1 := by
  change (cosliceSquareDiagramMap (pushoutSpan s.square) ≫
    evaluateFunctorAt (Y := dgNerve S (Complex S))
      (squareVertex (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])) 0 0)).app _
        (s.postcomposeSliceEdge q).edge = _
  rw [cosliceSquareDiagramMap_sourceEvaluation]
  rfl

/-- 始点を前合成する四角形比較の始点成分は指定射 p。 -/
lemma precomposeSquareEdge_source (p : V ⟶ A) :
    ((s.precomposeSquareEdge p).map ((truncation 2).map
      (evaluateFunctorAt (Y := dgNerve S (Complex S))
        (squareVertex (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])) 0 0)))).edge =
      (complexEdge p).edge := by
  change (sliceSquareDiagramMap (pullbackCospan s.square) ≫
    evaluateFunctorAt (Y := dgNerve S (Complex S))
      (squareVertex (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])) 0 0)).app _
        (s.precomposeSliceEdge p).edge = _
  rw [sliceSquareDiagramMap_sourceEvaluation]
  exact s.precomposeSliceEdge_projection p

/-- 始点を前合成する四角形比較の終点成分は定値辺。 -/
lemma precomposeSquareEdge_target (p : V ⟶ A) :
    ((s.precomposeSquareEdge p).map ((truncation 2).map
      (evaluateFunctorAt (Y := dgNerve S (Complex S))
        (squareVertex (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])) 1 1)))).edge =
      PinchedHom.constant ((pullbackCospan s.square).app (Opposite.op ⦋0⦌)
        cospanTargetVertex) 1 := by
  change (sliceSquareDiagramMap (pullbackCospan s.square) ≫
    evaluateFunctorAt (Y := dgNerve S (Complex S))
      (squareVertex (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])) 1 1)).app _
        (s.precomposeSliceEdge p).edge = _
  rw [sliceSquareDiagramMap_targetEvaluation]
  rfl

end SerrePositivity.InfinityCategories.ComplexSquareData
