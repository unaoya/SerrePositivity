module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFiberBoundaryTriangles
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DataLowDimensionalPullback

/-! # fiber の実境界から回収する対象と斉次成分

概要：最後に標準 fiber の錐を持つ境界から、対象・射影・元の射・零成分を回収する。
方針：最後の三角形の一致を各頂点・辺・三点成分で評価する。
規約：全 Hom end の成分を使う。使われ方：β3 の実残差の型付き移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D} {n : ℕ} (f : M ⟶ N)
variable (b : (SSet.boundary (n + 1) : SSet) ⟶
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
variable (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
  SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f))
include hb

/-- left の境界データの apex 対象の同定。 -/
lemma dgModuleFiberBoundary_left_apex :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f := by
  have h := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A D) 2 => s.obj (0 : Fin 3))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_left_triangle A D f b hb)
  exact h

/-- left の境界データの M 対象の同定。 -/
lemma dgModuleFiberBoundary_left_M :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) =
      ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M := by
  have h := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A D) 2 => s.obj (1 : Fin 3))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_left_triangle A D f b hb)
  exact h

/-- left の境界データの N 対象の同定。 -/
lemma dgModuleFiberBoundary_left_N :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) =
      ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N := by
  have h := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A D) 2 => s.obj (2 : Fin 3))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_left_triangle A D f b hb)
  exact h

/-- left の projection 辺は指定した全 Hom end の成分。 -/
lemma dgModuleFiberBoundary_left_projection_heq :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).edgeHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjectionElement A D f) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom_injective (n + 1)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_left_triangle A D f b hb)
    (0 : Fin 3) 1 (by decide) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n)
  exact h.trans (heq_of_eq (show
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberLowerTriangle A D f).simplex.toSimplexData.edgeHom 0 1 (by decide) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjectionElement A D f from by
      change (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f))).val = _
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection_cycle A D f))

/-- left の cospan 辺は指定した全 Hom end の成分。 -/
lemma dgModuleFiberBoundary_left_cospan_heq :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).edgeHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n))
      ((_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom_injective (n + 1)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_left_triangle A D f b hb)
    (1 : Fin 3) 2 (by decide) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)
  exact h.trans (heq_of_eq (show
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberLowerTriangle A D f).simplex.toSimplexData.edgeHom 1 2 (by decide) =
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val from rfl))

/-- left の diagonal 辺は指定した全 Hom end の成分。 -/
lemma dgModuleFiberBoundary_left_diagonal_heq :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).edgeHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n))))
      ((0 : GradedHom A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f) (ForgetEnrichment.to (Complex A) N) 0)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom_injective (n + 1)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_left_triangle A D f b hb)
    (0 : Fin 3) 2 (by decide) (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)))
  exact h.trans (heq_of_eq (show
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberLowerTriangle A D f).simplex.toSimplexData.edgeHom 0 2 (by decide) =
      (0 : GradedHom A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f) (ForgetEnrichment.to (Complex A) N) 0) from rfl))

/-- left の三点成分は指定した零ホモトピー成分。 -/
lemma dgModuleFiberBoundary_left_homotopy_heq :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).tripleHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D f) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleHom_heq_of_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom_injective (n + 1)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_left_triangle A D f b hb)
    (0 : Fin 3) 1 2 (by decide) (by decide)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)
  exact h.trans (heq_of_eq (show
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberLowerTriangle A D f).simplex.toSimplexData.tripleHom 0 1 2
      (by decide) (by decide) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D f from rfl))

/-- right の境界データの apex 対象の同定。 -/
lemma dgModuleFiberBoundary_right_apex :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f := by
  have h := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A D) 2 => s.obj (0 : Fin 3))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_right_triangle A D f b hb)
  exact h

/-- right の境界データの zero 対象の同定。 -/
lemma dgModuleFiberBoundary_right_zero :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) =
      ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleZero A D) := by
  have h := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A D) 2 => s.obj (1 : Fin 3))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_right_triangle A D f b hb)
  exact h

/-- right の境界データの N 対象の同定。 -/
lemma dgModuleFiberBoundary_right_N :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) =
      ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N := by
  have h := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A D) 2 => s.obj (2 : Fin 3))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_right_triangle A D f b hb)
  exact h

/-- right の projection 辺は指定した全 Hom end の成分。 -/
lemma dgModuleFiberBoundary_right_projection_heq :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).edgeHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n))
      ((0 : GradedHom A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f) (ForgetEnrichment.to (Complex A) (moduleZero A D))
        0)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom_injective (n + 1)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_right_triangle A D f b hb)
    (0 : Fin 3) 1 (by decide) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n)
  exact h.trans (heq_of_eq (show
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberUpperTriangle A D f).simplex.toSimplexData.edgeHom 0 1 (by decide) =
      (0 : GradedHom A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f) (ForgetEnrichment.to (Complex A) (moduleZero A D)) 0)
        from rfl))

/-- right の cospan 辺は指定した全 Hom end の成分。 -/
lemma dgModuleFiberBoundary_right_cospan_heq :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).edgeHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n))
      ((0 : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleZero A D)) (ForgetEnrichment.to
        (_root_.SerrePositivity.DifferentialGraded.Complex A) N) 0)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom_injective (n + 1)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_right_triangle A D f b hb)
    (1 : Fin 3) 2 (by decide) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)
  exact h.trans (heq_of_eq (show
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberUpperTriangle A D f).simplex.toSimplexData.edgeHom 1 2 (by decide) =
      (0 : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleZero A D)) (ForgetEnrichment.to
        (_root_.SerrePositivity.DifferentialGraded.Complex A) N) 0) from rfl))

/-- right の diagonal 辺は指定した全 Hom end の成分。 -/
lemma dgModuleFiberBoundary_right_diagonal_heq :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).edgeHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n))))
      ((0 : GradedHom A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f) (ForgetEnrichment.to (Complex A) N) 0)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom_injective (n + 1)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_right_triangle A D f b hb)
    (0 : Fin 3) 2 (by decide) (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)))
  exact h.trans (heq_of_eq (show
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberUpperTriangle A D f).simplex.toSimplexData.edgeHom 0 2 (by decide) =
      (0 : GradedHom A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f) (ForgetEnrichment.to (Complex A) N) 0) from rfl))

/-- right の三点成分は指定した零ホモトピー成分。 -/
lemma dgModuleFiberBoundary_right_homotopy_heq :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).tripleHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n))
      ((0 : GradedHom A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f) (ForgetEnrichment.to (Complex A) N) (-1))) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleHom_heq_of_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom_injective (n + 1)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_right_triangle A D f b hb)
    (0 : Fin 3) 1 2 (by decide) (by decide)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)
  exact h.trans (heq_of_eq (show
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberUpperTriangle A D f).simplex.toSimplexData.tripleHom 0 1 2
      (by decide) (by decide) = (0 : GradedHom A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f) (ForgetEnrichment.to
        (_root_.SerrePositivity.DifferentialGraded.Complex A) N) (-1)) from rfl))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
