module

public import SerrePositivity.InfinityCategories.F2.Idempotent.BicartesianZeroSquares
public import SerrePositivity.InfinityCategories.F1.SuspensionDiagramArrows
public import SerrePositivity.InfinityCategories.Core.ZeroTargetArrows
public import SerrePositivity.InfinityCategories.Stable.SpanFamilies
public import SerrePositivity.InfinityCategories.F1.ColimitCoconeFamilies

/-!
概要：元の双カルテジアン零角四角形の全族から、零枝と全普遍余錐の族を回収する。
方針：元の四角形を左辺と全 span 余錐に制限し、元の頂点条件で全部分圏へ因子化。
規約：元の全族を保持し、射影との厳密な可換性を公開する。
使われ方：元の下辺射影の正次元境界充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の全四角形の族を、同じ零終点を持つ左辺の全族へ制限する。 -/
def bicartesianZeroLeftArrow (X : SSet.{u}) :
    bicartesianZeroSquares X ⟶ zeroTargetArrows X :=
  fullSubcomplexLift IsZeroTargetArrow
    ((fullSubcomplexOnVertices _ IsBicartesianZeroVertex).ι ≫ (pre squareLeftEdge).app X) (by
      intro v
      let F := (functorVertexEquiv ((Δ[1] : SSet.{u}) ⊗ Δ[1]) X).symm v.val
      have hF : functorVertex F = v.val := (functorVertexEquiv _ _).apply_symm_apply _
      have hv := fullSubcomplexOnVertices_vertex v
      change IsBicartesianZeroVertex v.val at hv
      rw [← hF, isBicartesianZeroVertex_functorVertex] at hv
      change IsZeroTargetArrow (((pre squareLeftEdge).app X).app (Opposite.op ⦋0⦌) v.val)
      rw [← hF]
      change IsZeroVertex ((evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app
        (Opposite.op ⦋0⦌) (functorVertex (squareLeftEdge ≫ F)))
      rw [evaluateFunctorAt_functorVertex]
      exact hv.1)

/-- 左辺の全部分圏への因子化は、同じ元の左辺制限を厳密に回収する。 -/
lemma bicartesianZeroLeftArrow_inclusion (X : SSet.{u}) :
    bicartesianZeroLeftArrow X ≫
      (fullSubcomplexOnVertices ((ihom (Δ[1] : SSet.{u})).obj X) IsZeroTargetArrow).ι =
    (fullSubcomplexOnVertices _ IsBicartesianZeroVertex).ι ≫ (pre squareLeftEdge).app X :=
  fullSubcomplexLift_ι _ _ _

/-- 元の左辺と下辺の全族は、同じ始点の全族を持つ。 -/
lemma bicartesianZeroLeftArrow_source (X : SSet.{u}) :
    bicartesianZeroLeftArrow X ≫ zeroTargetArrowSource X =
      bicartesianZeroBottomProjection X ≫
        evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  rw [zeroTargetArrowSource, ← Category.assoc, bicartesianZeroLeftArrow_inclusion,
    Category.assoc, stable_pre_evaluateFunctorAt, bicartesianZeroBottomProjection,
    Category.assoc, stable_pre_evaluateFunctorAt]
  rfl

/-- 元の全四角形の族を、同じ span の全普遍余錐の族へ制限する。 -/
def bicartesianZeroCoconeMap (X : SSet.{u}) [Quasicategory X] :
    bicartesianZeroSquares X ⟶ colimitCocones (horn 2 0 : SSet.{u}) X :=
  fullSubcomplexLift (InitialBoundaryLifting (coconeRestriction (horn 2 0 : SSet.{u}) X))
    ((fullSubcomplexOnVertices _ IsBicartesianZeroVertex).ι ≫
      (pre spanCoconeSquareIso.hom).app X) (by
      intro v
      let F := (functorVertexEquiv ((Δ[1] : SSet.{u}) ⊗ Δ[1]) X).symm v.val
      have hF : functorVertex F = v.val := (functorVertexEquiv _ _).apply_symm_apply _
      have hv := fullSubcomplexOnVertices_vertex v
      change IsBicartesianZeroVertex v.val at hv
      rw [← hF, isBicartesianZeroVertex_functorVertex] at hv
      change InitialBoundaryLifting (coconeRestriction (horn 2 0 : SSet.{u}) X)
        (((pre spanCoconeSquareIso.hom).app X).app (Opposite.op ⦋0⦌) v.val)
      rw [← hF]
      exact hv.2.2.initialBoundaryLifting)

/-- 元の全普遍余錐への因子化は、元の四角形の全余錐表示を厳密に回収する。 -/
lemma bicartesianZeroCoconeMap_inclusion (X : SSet.{u}) [Quasicategory X] :
    bicartesianZeroCoconeMap X ≫
      (relativeInitialVertices (coconeRestriction (horn 2 0 : SSet.{u}) X)).ι =
    (fullSubcomplexOnVertices _ IsBicartesianZeroVertex).ι ≫
      (pre spanCoconeSquareIso.hom).app X := fullSubcomplexLift_ι _ _ _

/-- 元の全普遍余錐を元の span に制限すると、同じ元の四角形の span 制限になる。 -/
lemma bicartesianZeroCoconeMap_projection (X : SSet.{u}) [Quasicategory X] :
    bicartesianZeroCoconeMap X ≫ colimitCoconeProjection (horn 2 0 : SSet.{u}) X =
      (fullSubcomplexOnVertices _ IsBicartesianZeroVertex).ι ≫ (pre spanSquareBoundary).app X := by
  rw [colimitCoconeProjection, relativeInitialProjection, ← Category.assoc,
    bicartesianZeroCoconeMap_inclusion, Category.assoc, coconeRestriction,
    ← NatTrans.comp_app, ← pre_map]
  rfl

end SerrePositivity.InfinityCategories.F2.Idempotent
