module
public import SerrePositivity.InfinityCategories.Stable.CospanFamilies
public import SerrePositivity.InfinityCategories.Core.LimitConeFamilies
public import SerrePositivity.InfinityCategories.Stable.SuspensionDiagramArrows

/-! # Loop 図式の入力の二辺

概要：loop 四角形の二つの終点側の辺は、零対象から出る辺の族をなす。
方針：辺の包含による前合成を全部分圏へ制限し、終点評価との可換性を計算する。
規約：零対象と引き戻し性の頂点条件を用いる。
使われ方：S3 の loop 四角形の相対境界充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：loop 図式の右辺は零対象から出る辺の族。
方針：右辺に制限し、右下の零頂点条件を使う。
規約：始点は右下、終点は右上。
使われ方：cospan の第一辺の相対延長。 -/
def loopDiagramRightArrow (X : SSet.{u}) : loopDiagrams X ⟶ zeroSourceArrows X :=
  fullSubcomplexLift IsZeroSourceArrow
    ((fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι ≫ (pre squareRightEdge).app X)
    (by
      intro v
      have hz := (fullSubcomplexOnVertices_vertex v).2.1
      have hF : functorVertex (squareDiagram v.val) = v.val :=
        (functorVertexEquiv _ _).apply_symm_apply _
      change IsZeroSourceArrow (((pre squareRightEdge).app X).app (Opposite.op ⦋0⦌) v.val)
      rw [← hF]
      change IsZeroSourceArrow (functorVertex (squareRightEdge ≫ squareDiagram v.val))
      unfold IsZeroSourceArrow
      rw [evaluateFunctorAt_functorVertex]
      exact hz)

/-- 概要：loop 図式の上辺は零対象から出る辺の族。
方針：上辺に制限し、左上の零頂点条件を使う。
規約：始点は左上、終点は右上。
使われ方：cospan の第二辺の相対延長。 -/
def loopDiagramTopArrow (X : SSet.{u}) : loopDiagrams X ⟶ zeroSourceArrows X :=
  fullSubcomplexLift IsZeroSourceArrow
    ((fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι ≫ (pre squareTopEdge).app X)
    (by
      intro v
      have hz := (fullSubcomplexOnVertices_vertex v).1
      have hF : functorVertex (squareDiagram v.val) = v.val :=
        (functorVertexEquiv _ _).apply_symm_apply _
      change IsZeroSourceArrow (((pre squareTopEdge).app X).app (Opposite.op ⦋0⦌) v.val)
      rw [← hF]
      change IsZeroSourceArrow (functorVertex (squareTopEdge ≫ squareDiagram v.val))
      unfold IsZeroSourceArrow
      rw [evaluateFunctorAt_functorVertex]
      exact hz)

/-- 概要：右辺の終点評価は四角形の右上の評価。
方針：前合成と評価の式を使う。
規約：厳密な等式。
使われ方：終点を固定した辺の持ち上げ。 -/
lemma loopDiagramRightArrow_target (X : SSet.{u}) :
    loopDiagramRightArrow X ≫ zeroSourceArrowTarget X =
      loopDiagramEvaluation X 1 1 := by
  change (loopDiagramRightArrow X ≫
    (fullSubcomplexOnVertices _ IsZeroSourceArrow).ι) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = _
  rw [loopDiagramRightArrow, fullSubcomplexLift_ι, Category.assoc,
    stable_pre_evaluateFunctorAt]
  rfl

/-- 概要：上辺の終点評価は四角形の右上の評価。
方針：前合成と評価の式を使う。
規約：厳密な等式。
使われ方：終点を固定した辺の持ち上げ。 -/
lemma loopDiagramTopArrow_target (X : SSet.{u}) :
    loopDiagramTopArrow X ≫ zeroSourceArrowTarget X =
      loopDiagramEvaluation X 1 1 := by
  change (loopDiagramTopArrow X ≫
    (fullSubcomplexOnVertices _ IsZeroSourceArrow).ι) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = _
  rw [loopDiagramTopArrow, fullSubcomplexLift_ι, Category.assoc,
    stable_pre_evaluateFunctorAt]
  rfl

/-- 概要：loop 四角形の族をその cospan の普遍錐の族へ送る。
方針：正方形の join 表示で前合成し、引き戻し性を相対始対象性へ移す。
規約：値域は quasicategory。
使われ方：終点と cospan を持ち上げた後の普遍四角形の延長。 -/
def loopDiagramConeFamily (X : SSet.{u}) [Quasicategory X] :
    loopDiagrams X ⟶ limitCones (horn 2 2 : SSet.{u}) X :=
  fullSubcomplexLift (TerminalBoundaryLifting (coneRestriction (horn 2 2 : SSet.{u}) X))
    ((fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι ≫
      (pre cospanConeSquareIso.hom).app X) (by
    intro v
    have hp := (fullSubcomplexOnVertices_vertex v).2.2
    have hF : functorVertex (squareDiagram v.val) = v.val :=
      (functorVertexEquiv _ _).apply_symm_apply _
    change TerminalBoundaryLifting (coneRestriction (horn 2 2 : SSet.{u}) X)
      (((pre cospanConeSquareIso.hom).app X).app (Opposite.op ⦋0⦌) v.val)
    rw [← hF]
    exact terminalBoundaryLifting_coneRestriction_of_isLimitCone
      (pullbackCone (squareDiagram v.val)) hp)

/-- 概要：錐の族の包含は正方形の join 表示による前合成。
方針：全部分複体への持ち上げの値を取る。
規約：厳密な等式。
使われ方：四角形の族の境界の復元。 -/
lemma loopDiagramConeFamily_ι (X : SSet.{u}) [Quasicategory X] :
    loopDiagramConeFamily X ≫
      (relativeTerminalVertices (coneRestriction (horn 2 2 : SSet.{u}) X)).ι =
      (fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι ≫
        (pre cospanConeSquareIso.hom).app X := rfl

/-- 概要：普遍錐の図式への制限は元の四角形の cospan への制限。
方針：前合成の合成則と cospan の包含の定義を使う。
規約：厳密な等式。
使われ方：普遍錐の相対境界の可換条件。 -/
lemma loopDiagramConeFamily_projection (X : SSet.{u}) [Quasicategory X] :
    loopDiagramConeFamily X ≫ limitConeProjection (horn 2 2 : SSet.{u}) X =
      (fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι ≫
        (pre cospanSquareBoundary).app X := by
  change (loopDiagramConeFamily X ≫
    (relativeTerminalVertices (coneRestriction (horn 2 2 : SSet.{u}) X)).ι) ≫
      (pre (joinInr Δ[0] (horn 2 2 : SSet.{u}))).app X = _
  rw [loopDiagramConeFamily_ι, Category.assoc,
    ← NatTrans.comp_app, ← pre_map]
  rfl

end SerrePositivity.InfinityCategories
