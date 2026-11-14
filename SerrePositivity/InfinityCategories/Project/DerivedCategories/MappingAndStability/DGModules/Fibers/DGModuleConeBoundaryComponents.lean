module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleConeBoundaryTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanTwoPrefixIndex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DataLowDimensionalPullback

/-! # 標準 cofiber 余錐から回収した対象と成分

概要：最初の頂点に標準 cofiber 余錐を持つ境界データの対象・三辺・三点成分を同定する。
方針：回収した最初の三角形の等式を対象と斉次成分で評価する。
規約：任意の非有界複体。使われ方：D7 の残差を cofiber の Hom 座標へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 概要：左の境界データの A 頂点の対象は標準余錐の指定対象。
方針：最初の三角形の等式を対応する頂点で評価する。
規約：追加の選択を使わない。使われ方：残差の端点の型の移送。 -/
lemma dgModuleConeBoundary_left_A {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)).obj 0 = (ForgetEnrichment.to (Complex A)
      M) := by
  have H := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A D) 2 => s.obj (0 : Fin 3))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_left_triangle A D f b hb)
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)).obj 0 = (ForgetEnrichment.to (Complex
    A) M) at H
  exact H

/-- 概要：左の境界データの B 頂点の対象は標準余錐の指定対象。
方針：最初の三角形の等式を対応する頂点で評価する。
規約：追加の選択を使わない。使われ方：残差の端点の型の移送。 -/
lemma dgModuleConeBoundary_left_B {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) =
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N) := by
  have H := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A D) 2 => s.obj (1 : Fin 3))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_left_triangle A D f b hb)
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) =
    (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N) at H
  exact H

/-- 概要：左の境界データの apex 頂点の対象は標準余錐の指定対象。
方針：最初の三角形の等式を対応する頂点で評価する。
規約：追加の選択を使わない。使われ方：残差の端点の型の移送。 -/
lemma dgModuleConeBoundary_left_apex {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) = (ForgetEnrichment.to
      (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) := by
  have H := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A D) 2 => s.obj (2 : Fin 3))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_left_triangle A D f b hb)
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) =
    (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) at H
  exact H

/-- 概要：左の境界データの span 辺の成分は指定された鎖写像の cochain。
方針：最初の三角形への単射の制限を二点成分で評価する。
規約：対象の等号の移送を異種等号に含める。使われ方：脚との残差合成の同定。 -/
lemma dgModuleConeBoundary_left_span_heq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)).edgeHom
      0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n))
      ((_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val) := by
  have H := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom_injective (n + 1)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_left_triangle A D f b hb)
    (0 : Fin 3) 1 (by decide) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n)
  exact H.trans (heq_of_eq (show
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeLowerTriangle A D f).simplex.toSimplexData.edgeHom 0 1 (by decide) =
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val from rfl))

/-- 概要：左の境界データの inclusion 辺の成分は指定された鎖写像の cochain。
方針：最初の三角形への単射の制限を二点成分で評価する。
規約：対象の等号の移送を異種等号に含める。使われ方：脚との残差合成の同定。 -/
lemma dgModuleConeBoundary_left_inclusion_heq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)).edgeHom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n))
      ((_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleConeInr A D f))).val) := by
  have H := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom_injective (n + 1)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_left_triangle A D f b hb)
    (1 : Fin 3) 2 (by decide) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)
  exact H.trans (heq_of_eq (show
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeLowerTriangle A D f).simplex.toSimplexData.edgeHom 1 2 (by decide) =
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleConeInr A D f))).val from rfl))

/-- 概要：左の境界データの diagonal 辺の成分は指定された鎖写像の cochain。
方針：最初の三角形への単射の制限を二点成分で評価する。
規約：対象の等号の移送を異種等号に含める。使われ方：脚との残差合成の同定。 -/
lemma dgModuleConeBoundary_left_diagonal_heq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)).edgeHom 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n))
      ((0 : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A)
        (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) 0)) := by
  have H := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom_injective (n + 1)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_left_triangle A D f b hb)
    (0 : Fin 3) 2 (by decide) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)
  exact H.trans (heq_of_eq (show
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeLowerTriangle A D f).simplex.toSimplexData.edgeHom 0 2 (by decide) =
      (0 : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A)
        (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) 0) from rfl))

/-- 概要：左の境界データの三点成分は指定された標準余錐のホモトピー。
方針：最初の三角形への単射の制限を三点成分で評価する。
規約：次数は −1。使われ方：三角形側の残差合成の同定。 -/
lemma dgModuleConeBoundary_left_homotopy_heq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)).tripleHom
      0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n))
      (_root_.SerrePositivity.DifferentialGraded.moduleConeInlElement A D f) := by
  have H := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleHom_heq_of_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom_injective (n + 1)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_left_triangle A D f b hb)
    (0 : Fin 3) 1 2 (by decide) (by decide)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)
  exact H.trans (heq_of_eq (show
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeLowerTriangle A D f).simplex.toSimplexData.tripleHom
      0 1 2 (by decide) (by decide) =
      _root_.SerrePositivity.DifferentialGraded.moduleConeInlElement A D f from rfl))

/-- 概要：右の境界データの A 頂点の対象は標準余錐の指定対象。
方針：最初の三角形の等式を対応する頂点で評価する。
規約：追加の選択を使わない。使われ方：残差の端点の型の移送。 -/
lemma dgModuleConeBoundary_right_A {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)).obj 0 = (ForgetEnrichment.to (Complex A)
      M) := by
  have H := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A D) 2 => s.obj (0 : Fin 3))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_right_triangle A D f b hb)
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)).obj 0 = (ForgetEnrichment.to
    (_root_.SerrePositivity.DifferentialGraded.Complex A) M) at H
  exact H

/-- 概要：右の境界データの C 頂点の対象は標準余錐の指定対象。
方針：最初の三角形の等式を対応する頂点で評価する。
規約：追加の選択を使わない。使われ方：残差の端点の型の移送。 -/
lemma dgModuleConeBoundary_right_C {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) = zeroModule A D
      := by
  have H := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A D) 2 => s.obj (1 : Fin 3))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_right_triangle A D f b hb)
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) =
    _root_.SerrePositivity.DifferentialGraded.zeroModule A D at H
  exact H

/-- 概要：右の境界データの apex 頂点の対象は標準余錐の指定対象。
方針：最初の三角形の等式を対応する頂点で評価する。
規約：追加の選択を使わない。使われ方：残差の端点の型の移送。 -/
lemma dgModuleConeBoundary_right_apex {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) = (ForgetEnrichment.to
      (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) := by
  have H := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A D) 2 => s.obj (2 : Fin 3))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_right_triangle A D f b hb)
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) =
    (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) at H
  exact H

/-- 概要：右の境界データの span 辺の成分は指定された鎖写像の cochain。
方針：最初の三角形への単射の制限を二点成分で評価する。
規約：対象の等号の移送を異種等号に含める。使われ方：脚との残差合成の同定。 -/
lemma dgModuleConeBoundary_right_span_heq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)).edgeHom
      0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n))
      ((0 : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M) (_root_.SerrePositivity.DifferentialGraded.zeroModule A D) 0)) := by
  have H := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom_injective (n + 1)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_right_triangle A D f b hb)
    (0 : Fin 3) 1 (by decide) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n)
  exact H.trans (heq_of_eq (show
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeUpperTriangle A D f).simplex.toSimplexData.edgeHom 0 1 (by decide) =
      (0 : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M) (_root_.SerrePositivity.DifferentialGraded.zeroModule A D) 0) from rfl))

/-- 概要：右の境界データの inclusion 辺の成分は指定された鎖写像の cochain。
方針：最初の三角形への単射の制限を二点成分で評価する。
規約：対象の等号の移送を異種等号に含める。使われ方：脚との残差合成の同定。 -/
lemma dgModuleConeBoundary_right_inclusion_heq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)).edgeHom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n))
      ((0 : _root_.SerrePositivity.DifferentialGraded.GradedHom A (_root_.SerrePositivity.DifferentialGraded.zeroModule A D) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f))
        0)) := by
  have H := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom_injective (n + 1)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_right_triangle A D f b hb)
    (1 : Fin 3) 2 (by decide) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)
  exact H.trans (heq_of_eq (show
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeUpperTriangle A D f).simplex.toSimplexData.edgeHom 1 2 (by decide) =
      (0 : _root_.SerrePositivity.DifferentialGraded.GradedHom A (_root_.SerrePositivity.DifferentialGraded.zeroModule A D) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) 0)
        from rfl))

/-- 概要：右の境界データの diagonal 辺の成分は指定された鎖写像の cochain。
方針：最初の三角形への単射の制限を二点成分で評価する。
規約：対象の等号の移送を異種等号に含める。使われ方：脚との残差合成の同定。 -/
lemma dgModuleConeBoundary_right_diagonal_heq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)).edgeHom 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n))
      ((0 : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A)
        (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) 0)) := by
  have H := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom_injective (n + 1)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_right_triangle A D f b hb)
    (0 : Fin 3) 2 (by decide) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)
  exact H.trans (heq_of_eq (show
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeUpperTriangle A D f).simplex.toSimplexData.edgeHom 0 2 (by decide) =
      (0 : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A)
        (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) 0) from rfl))

/-- 概要：右の境界データの三点成分は指定された標準余錐のホモトピー。
方針：最初の三角形への単射の制限を三点成分で評価する。
規約：次数は −1。使われ方：三角形側の残差合成の同定。 -/
lemma dgModuleConeBoundary_right_homotopy_heq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)).tripleHom
      0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n))
      ((0 : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A)
        (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) (-1))) := by
  have H := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleHom_heq_of_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom_injective (n + 1)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_right_triangle A D f b hb)
    (0 : Fin 3) 1 2 (by decide) (by decide)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)
  exact H.trans (heq_of_eq (show
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeUpperTriangle A D f).simplex.toSimplexData.tripleHom
      0 1 2 (by decide) (by decide) =
      (0 : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A)
        (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) (-1)) from rfl))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
