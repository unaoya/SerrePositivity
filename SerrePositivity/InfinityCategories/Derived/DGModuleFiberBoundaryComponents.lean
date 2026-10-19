module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberBoundaryTriangles
public import SerrePositivity.InfinityCategories.DGNerve.DataLowDimensionalPullback

/-! # fiber の実境界から回収する対象と斉次成分

概要：最後に標準 fiber の錐を持つ境界から、対象・射影・元の射・零成分を回収する。
方針：最後の三角形の一致を各頂点・辺・三点成分で評価する。
規約：全 Hom end の成分を使う。使われ方：β3 の実残差の型付き移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D} {n : ℕ} (f : M ⟶ N)
variable (b : (SSet.boundary (n + 1) : SSet) ⟶
  sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
variable (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
  SSet.yonedaEquiv.symm (dgModuleFiberCone A D f))
include hb

/-- left の境界データの apex 対象の同定。 -/
lemma dgModuleFiberBoundary_left_apex :
    (cospanBoundaryLeftZeroData (sliceOverUncurry b)).obj (cospanApex n) =
      dgModuleFiber A D f := by
  have h := congrArg (fun s : SimplexData A (RightModule A D) 2 => s.obj (0 : Fin 3))
    (dgModuleFiberBoundary_left_triangle A D f b hb)
  exact h

/-- left の境界データの M 対象の同定。 -/
lemma dgModuleFiberBoundary_left_M :
    (cospanBoundaryLeftZeroData (sliceOverUncurry b)).obj (cospanFirstTail n) =
      ForgetEnrichment.to (Complex A) M := by
  have h := congrArg (fun s : SimplexData A (RightModule A D) 2 => s.obj (1 : Fin 3))
    (dgModuleFiberBoundary_left_triangle A D f b hb)
  exact h

/-- left の境界データの N 対象の同定。 -/
lemma dgModuleFiberBoundary_left_N :
    (cospanBoundaryLeftZeroData (sliceOverUncurry b)).obj (cospanLastTail n) =
      ForgetEnrichment.to (Complex A) N := by
  have h := congrArg (fun s : SimplexData A (RightModule A D) 2 => s.obj (2 : Fin 3))
    (dgModuleFiberBoundary_left_triangle A D f b hb)
  exact h

/-- left の projection 辺は指定した全 Hom end の成分。 -/
lemma dgModuleFiberBoundary_left_projection_heq :
    HEq ((cospanBoundaryLeftZeroData (sliceOverUncurry b)).edgeHom
      (cospanApex n) (cospanFirstTail n) (cospanApex_lt_firstTail n))
      (dgModuleFiberProjectionElement A D f) := by
  have h := SimplexData.edgeHom_heq_of_pullback_eq _ _ (lastTriangleOrderHom (n + 1))
    (lastTriangleOrderHom_injective (n + 1)) (dgModuleFiberBoundary_left_triangle A D f b hb)
    (0 : Fin 3) 1 (by decide) (cospanApex_lt_firstTail n)
  exact h.trans (heq_of_eq (show
    (dgModuleFiberLowerTriangle A D f).simplex.toSimplexData.edgeHom 0 1 (by decide) =
      dgModuleFiberProjectionElement A D f from by
      change (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (dgModuleFiberProjection A D f))).val = _
      exact dgModuleFiberProjection_cycle A D f))

/-- left の cospan 辺は指定した全 Hom end の成分。 -/
lemma dgModuleFiberBoundary_left_cospan_heq :
    HEq ((cospanBoundaryLeftZeroData (sliceOverUncurry b)).edgeHom
      (cospanFirstTail n) (cospanLastTail n) (cospanFirstTail_lt_lastTail n))
      ((cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val) := by
  have h := SimplexData.edgeHom_heq_of_pullback_eq _ _ (lastTriangleOrderHom (n + 1))
    (lastTriangleOrderHom_injective (n + 1)) (dgModuleFiberBoundary_left_triangle A D f b hb)
    (1 : Fin 3) 2 (by decide) (cospanFirstTail_lt_lastTail n)
  exact h.trans (heq_of_eq (show
    (dgModuleFiberLowerTriangle A D f).simplex.toSimplexData.edgeHom 1 2 (by decide) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val from rfl))

/-- left の diagonal 辺は指定した全 Hom end の成分。 -/
lemma dgModuleFiberBoundary_left_diagonal_heq :
    HEq ((cospanBoundaryLeftZeroData (sliceOverUncurry b)).edgeHom
      (cospanApex n) (cospanLastTail n) (((cospanApex_lt_firstTail n).trans
        (cospanFirstTail_lt_lastTail n))))
      ((0 : GradedHom A (dgModuleFiber A D f) (ForgetEnrichment.to (Complex A) N) 0)) := by
  have h := SimplexData.edgeHom_heq_of_pullback_eq _ _ (lastTriangleOrderHom (n + 1))
    (lastTriangleOrderHom_injective (n + 1)) (dgModuleFiberBoundary_left_triangle A D f b hb)
    (0 : Fin 3) 2 (by decide) (((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n)))
  exact h.trans (heq_of_eq (show
    (dgModuleFiberLowerTriangle A D f).simplex.toSimplexData.edgeHom 0 2 (by decide) =
      (0 : GradedHom A (dgModuleFiber A D f) (ForgetEnrichment.to (Complex A) N) 0) from rfl))

/-- left の三点成分は指定した零ホモトピー成分。 -/
lemma dgModuleFiberBoundary_left_homotopy_heq :
    HEq ((cospanBoundaryLeftZeroData (sliceOverUncurry b)).tripleHom
      (cospanApex n) (cospanFirstTail n) (cospanLastTail n)
      (cospanApex_lt_firstTail n) (cospanFirstTail_lt_lastTail n))
      (dgModuleFiberNullHomotopy A D f) := by
  have h := SimplexData.tripleHom_heq_of_pullback_eq _ _ (lastTriangleOrderHom (n + 1))
    (lastTriangleOrderHom_injective (n + 1)) (dgModuleFiberBoundary_left_triangle A D f b hb)
    (0 : Fin 3) 1 2 (by decide) (by decide)
    (cospanApex_lt_firstTail n) (cospanFirstTail_lt_lastTail n)
  exact h.trans (heq_of_eq (show
    (dgModuleFiberLowerTriangle A D f).simplex.toSimplexData.tripleHom 0 1 2
      (by decide) (by decide) = dgModuleFiberNullHomotopy A D f from rfl))

/-- right の境界データの apex 対象の同定。 -/
lemma dgModuleFiberBoundary_right_apex :
    (cospanBoundaryRightZeroData (sliceOverUncurry b)).obj (cospanApex n) =
      dgModuleFiber A D f := by
  have h := congrArg (fun s : SimplexData A (RightModule A D) 2 => s.obj (0 : Fin 3))
    (dgModuleFiberBoundary_right_triangle A D f b hb)
  exact h

/-- right の境界データの zero 対象の同定。 -/
lemma dgModuleFiberBoundary_right_zero :
    (cospanBoundaryRightZeroData (sliceOverUncurry b)).obj (cospanFirstTail n) =
      ForgetEnrichment.to (Complex A) (moduleZero A D) := by
  have h := congrArg (fun s : SimplexData A (RightModule A D) 2 => s.obj (1 : Fin 3))
    (dgModuleFiberBoundary_right_triangle A D f b hb)
  exact h

/-- right の境界データの N 対象の同定。 -/
lemma dgModuleFiberBoundary_right_N :
    (cospanBoundaryRightZeroData (sliceOverUncurry b)).obj (cospanLastTail n) =
      ForgetEnrichment.to (Complex A) N := by
  have h := congrArg (fun s : SimplexData A (RightModule A D) 2 => s.obj (2 : Fin 3))
    (dgModuleFiberBoundary_right_triangle A D f b hb)
  exact h

/-- right の projection 辺は指定した全 Hom end の成分。 -/
lemma dgModuleFiberBoundary_right_projection_heq :
    HEq ((cospanBoundaryRightZeroData (sliceOverUncurry b)).edgeHom
      (cospanApex n) (cospanFirstTail n) (cospanApex_lt_firstTail n))
      ((0 : GradedHom A (dgModuleFiber A D f) (ForgetEnrichment.to (Complex A) (moduleZero A D))
        0)) := by
  have h := SimplexData.edgeHom_heq_of_pullback_eq _ _ (lastTriangleOrderHom (n + 1))
    (lastTriangleOrderHom_injective (n + 1)) (dgModuleFiberBoundary_right_triangle A D f b hb)
    (0 : Fin 3) 1 (by decide) (cospanApex_lt_firstTail n)
  exact h.trans (heq_of_eq (show
    (dgModuleFiberUpperTriangle A D f).simplex.toSimplexData.edgeHom 0 1 (by decide) =
      (0 : GradedHom A (dgModuleFiber A D f) (ForgetEnrichment.to (Complex A) (moduleZero A D)) 0)
        from rfl))

/-- right の cospan 辺は指定した全 Hom end の成分。 -/
lemma dgModuleFiberBoundary_right_cospan_heq :
    HEq ((cospanBoundaryRightZeroData (sliceOverUncurry b)).edgeHom
      (cospanFirstTail n) (cospanLastTail n) (cospanFirstTail_lt_lastTail n))
      ((0 : GradedHom A (ForgetEnrichment.to (Complex A) (moduleZero A D)) (ForgetEnrichment.to
        (Complex A) N) 0)) := by
  have h := SimplexData.edgeHom_heq_of_pullback_eq _ _ (lastTriangleOrderHom (n + 1))
    (lastTriangleOrderHom_injective (n + 1)) (dgModuleFiberBoundary_right_triangle A D f b hb)
    (1 : Fin 3) 2 (by decide) (cospanFirstTail_lt_lastTail n)
  exact h.trans (heq_of_eq (show
    (dgModuleFiberUpperTriangle A D f).simplex.toSimplexData.edgeHom 1 2 (by decide) =
      (0 : GradedHom A (ForgetEnrichment.to (Complex A) (moduleZero A D)) (ForgetEnrichment.to
        (Complex A) N) 0) from rfl))

/-- right の diagonal 辺は指定した全 Hom end の成分。 -/
lemma dgModuleFiberBoundary_right_diagonal_heq :
    HEq ((cospanBoundaryRightZeroData (sliceOverUncurry b)).edgeHom
      (cospanApex n) (cospanLastTail n) (((cospanApex_lt_firstTail n).trans
        (cospanFirstTail_lt_lastTail n))))
      ((0 : GradedHom A (dgModuleFiber A D f) (ForgetEnrichment.to (Complex A) N) 0)) := by
  have h := SimplexData.edgeHom_heq_of_pullback_eq _ _ (lastTriangleOrderHom (n + 1))
    (lastTriangleOrderHom_injective (n + 1)) (dgModuleFiberBoundary_right_triangle A D f b hb)
    (0 : Fin 3) 2 (by decide) (((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n)))
  exact h.trans (heq_of_eq (show
    (dgModuleFiberUpperTriangle A D f).simplex.toSimplexData.edgeHom 0 2 (by decide) =
      (0 : GradedHom A (dgModuleFiber A D f) (ForgetEnrichment.to (Complex A) N) 0) from rfl))

/-- right の三点成分は指定した零ホモトピー成分。 -/
lemma dgModuleFiberBoundary_right_homotopy_heq :
    HEq ((cospanBoundaryRightZeroData (sliceOverUncurry b)).tripleHom
      (cospanApex n) (cospanFirstTail n) (cospanLastTail n)
      (cospanApex_lt_firstTail n) (cospanFirstTail_lt_lastTail n))
      ((0 : GradedHom A (dgModuleFiber A D f) (ForgetEnrichment.to (Complex A) N) (-1))) := by
  have h := SimplexData.tripleHom_heq_of_pullback_eq _ _ (lastTriangleOrderHom (n + 1))
    (lastTriangleOrderHom_injective (n + 1)) (dgModuleFiberBoundary_right_triangle A D f b hb)
    (0 : Fin 3) 1 2 (by decide) (by decide)
    (cospanApex_lt_firstTail n) (cospanFirstTail_lt_lastTail n)
  exact h.trans (heq_of_eq (show
    (dgModuleFiberUpperTriangle A D f).simplex.toSimplexData.tripleHom 0 1 2
      (by decide) (by decide) = (0 : GradedHom A (dgModuleFiber A D f) (ForgetEnrichment.to
        (Complex A) N) (-1)) from rfl))

end SerrePositivity.InfinityCategories
