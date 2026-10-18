module
public import SerrePositivity.InfinityCategories.Stable.SpanFamilies

/-! # Suspension 図式の入力の二辺

概要：suspension 四角形の二つの始点側の辺は、零対象へ向かう辺の族をなす。
方針：辺の包含による前合成を全部分圏へ制限し、始点評価との可換性を計算する。
規約：零対象と押し出し性の頂点条件を用いる。
使われ方：S3 の suspension 四角形の相対境界充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：前合成の後の評価は元の頂点の像での評価。
方針：各次数で頂点の定値単体の自然性を使う。
規約：単体集合の quasicategory 性は不要。
使われ方：四角形の辺と頂点の評価の整合。 -/
lemma stable_pre_evaluateFunctorAt {A B X : SSet.{u}} (i : A ⟶ B) (v : A _⦋0⦌) :
    (pre i).app X ≫ evaluateFunctorAt v =
      evaluateFunctorAt (Y := X) (i.app (Opposite.op ⦋0⦌) v) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro F
  change F.app (Opposite.op ⦋n⦌) (𝟙 _) (i.app _ (PinchedHom.constant v n)) = _
  rw [pinchedConstant_map]
  rfl

/-- 概要：suspension 図式の下辺は零対象へ向かう辺の族。
方針：下辺に制限し、右下の零頂点条件を使う。
規約：始点は左下、終点は右下。
使われ方：span の第一辺の相対延長。 -/
def suspensionDiagramBottomArrow (X : SSet.{u}) : suspensionDiagrams X ⟶ zeroTargetArrows X :=
  fullSubcomplexLift IsZeroTargetArrow
    ((fullSubcomplexOnVertices _ IsSuspensionDiagramVertex).ι ≫ (pre squareBottomEdge).app X)
    (by
      intro v
      have hz := (fullSubcomplexOnVertices_vertex v).2.1
      have hF : functorVertex (squareDiagram v.val) = v.val :=
        (functorVertexEquiv _ _).apply_symm_apply _
      change IsZeroTargetArrow (((pre squareBottomEdge).app X).app (Opposite.op ⦋0⦌) v.val)
      rw [← hF]
      change IsZeroTargetArrow (functorVertex (squareBottomEdge ≫ squareDiagram v.val))
      unfold IsZeroTargetArrow
      rw [evaluateFunctorAt_functorVertex]
      exact hz)

/-- 概要：suspension 図式の左辺は零対象へ向かう辺の族。
方針：左辺に制限し、左上の零頂点条件を使う。
規約：始点は左下、終点は左上。
使われ方：span の第二辺の相対延長。 -/
def suspensionDiagramLeftArrow (X : SSet.{u}) : suspensionDiagrams X ⟶ zeroTargetArrows X :=
  fullSubcomplexLift IsZeroTargetArrow
    ((fullSubcomplexOnVertices _ IsSuspensionDiagramVertex).ι ≫ (pre squareLeftEdge).app X)
    (by
      intro v
      have hz := (fullSubcomplexOnVertices_vertex v).1
      have hF : functorVertex (squareDiagram v.val) = v.val :=
        (functorVertexEquiv _ _).apply_symm_apply _
      change IsZeroTargetArrow (((pre squareLeftEdge).app X).app (Opposite.op ⦋0⦌) v.val)
      rw [← hF]
      change IsZeroTargetArrow (functorVertex (squareLeftEdge ≫ squareDiagram v.val))
      unfold IsZeroTargetArrow
      rw [evaluateFunctorAt_functorVertex]
      exact hz)

/-- 概要：下辺の始点評価は四角形の左下の評価。
方針：前合成と評価の式を使う。
規約：厳密な等式。
使われ方：始点を固定した辺の持ち上げ。 -/
lemma suspensionDiagramBottomArrow_source (X : SSet.{u}) :
    suspensionDiagramBottomArrow X ≫ zeroTargetArrowSource X =
      suspensionDiagramEvaluation X 0 0 := by
  change (suspensionDiagramBottomArrow X ≫
    (fullSubcomplexOnVertices _ IsZeroTargetArrow).ι) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = _
  rw [suspensionDiagramBottomArrow, fullSubcomplexLift_ι, Category.assoc,
    stable_pre_evaluateFunctorAt]
  rfl

/-- 概要：左辺の始点評価は四角形の左下の評価。
方針：前合成と評価の式を使う。
規約：厳密な等式。
使われ方：始点を固定した辺の持ち上げ。 -/
lemma suspensionDiagramLeftArrow_source (X : SSet.{u}) :
    suspensionDiagramLeftArrow X ≫ zeroTargetArrowSource X =
      suspensionDiagramEvaluation X 0 0 := by
  change (suspensionDiagramLeftArrow X ≫
    (fullSubcomplexOnVertices _ IsZeroTargetArrow).ι) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = _
  rw [suspensionDiagramLeftArrow, fullSubcomplexLift_ι, Category.assoc,
    stable_pre_evaluateFunctorAt]
  rfl

/-- 概要：suspension 四角形の族をその span の普遍余錐の族へ送る。
方針：正方形の join 表示で前合成し、押し出し性を相対始対象性へ移す。
規約：値域は quasicategory。
使われ方：始点と span を持ち上げた後の普遍四角形の延長。 -/
def suspensionDiagramCoconeFamily (X : SSet.{u}) [Quasicategory X] :
    suspensionDiagrams X ⟶ colimitCocones (horn 2 0 : SSet.{u}) X :=
  fullSubcomplexLift (InitialBoundaryLifting (coconeRestriction (horn 2 0 : SSet.{u}) X))
    ((fullSubcomplexOnVertices _ IsSuspensionDiagramVertex).ι ≫
      (pre spanCoconeSquareIso.hom).app X) (by
    intro v
    have hp := (fullSubcomplexOnVertices_vertex v).2.2
    have hF : functorVertex (squareDiagram v.val) = v.val :=
      (functorVertexEquiv _ _).apply_symm_apply _
    change InitialBoundaryLifting (coconeRestriction (horn 2 0 : SSet.{u}) X)
      (((pre spanCoconeSquareIso.hom).app X).app (Opposite.op ⦋0⦌) v.val)
    rw [← hF]
    exact hp.initialBoundaryLifting)

/-- 概要：余錐の族の包含は正方形の join 表示による前合成。
方針：全部分複体への持ち上げの値を取る。
規約：厳密な等式。
使われ方：四角形の族の境界の復元。 -/
lemma suspensionDiagramCoconeFamily_ι (X : SSet.{u}) [Quasicategory X] :
    suspensionDiagramCoconeFamily X ≫
      (relativeInitialVertices (coconeRestriction (horn 2 0 : SSet.{u}) X)).ι =
      (fullSubcomplexOnVertices _ IsSuspensionDiagramVertex).ι ≫
        (pre spanCoconeSquareIso.hom).app X := rfl

/-- 概要：普遍余錐の図式への制限は元の四角形の span への制限。
方針：前合成の合成則と span の包含の定義を使う。
規約：厳密な等式。
使われ方：普遍余錐の相対境界の可換条件。 -/
lemma suspensionDiagramCoconeFamily_projection (X : SSet.{u}) [Quasicategory X] :
    suspensionDiagramCoconeFamily X ≫ colimitCoconeProjection (horn 2 0 : SSet.{u}) X =
      (fullSubcomplexOnVertices _ IsSuspensionDiagramVertex).ι ≫
        (pre spanSquareBoundary).app X := by
  change (suspensionDiagramCoconeFamily X ≫
    (relativeInitialVertices (coconeRestriction (horn 2 0 : SSet.{u}) X)).ι) ≫
      (pre (joinInl (horn 2 0 : SSet.{u}) Δ[0])).app X = _
  rw [suspensionDiagramCoconeFamily_ι, Category.assoc,
    ← NatTrans.comp_app, ← pre_map]
  rfl

end SerrePositivity.InfinityCategories
