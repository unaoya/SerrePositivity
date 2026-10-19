module
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeBoundaryTriangles
public import SerrePositivity.InfinityCategories.Derived.SpanTwoPrefixIndex
public import SerrePositivity.InfinityCategories.DGNerve.DataLowDimensionalPullback

/-! # 標準 cofiber 余錐から回収した対象と成分

概要：最初の頂点に標準 cofiber 余錐を持つ境界データの対象・三辺・三点成分を同定する。
方針：回収した最初の三角形の等式を対象と斉次成分で評価する。
規約：任意の非有界複体。使われ方：D7 の残差を cofiber の Hom 座標へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Opposite DifferentialGraded DGNerve CochainComplex HomComplex
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 概要：左の境界データの A 頂点の対象は標準余錐の指定対象。
方針：最初の三角形の等式を対応する頂点で評価する。
規約：追加の選択を使わない。使われ方：残差の端点の型の移送。 -/
lemma dgModuleConeBoundary_left_A {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    (spanBoundaryLeftZeroData (sliceUnderUncurry b)).obj 0 = (ForgetEnrichment.to (Complex A)
      M) := by
  have H := congrArg (fun s : SimplexData A (RightModule A D) 2 => s.obj (0 : Fin 3))
    (dgModuleConeBoundary_left_triangle A D f b hb)
  change (spanBoundaryLeftZeroData (sliceUnderUncurry b)).obj 0 = (ForgetEnrichment.to (Complex
    A) M) at H
  exact H

/-- 概要：左の境界データの B 頂点の対象は標準余錐の指定対象。
方針：最初の三角形の等式を対応する頂点で評価する。
規約：追加の選択を使わない。使われ方：残差の端点の型の移送。 -/
lemma dgModuleConeBoundary_left_B {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    (spanBoundaryLeftZeroData (sliceUnderUncurry b)).obj (spanSecondPrefix n) =
      (ForgetEnrichment.to (Complex A) N) := by
  have H := congrArg (fun s : SimplexData A (RightModule A D) 2 => s.obj (1 : Fin 3))
    (dgModuleConeBoundary_left_triangle A D f b hb)
  change (spanBoundaryLeftZeroData (sliceUnderUncurry b)).obj (spanSecondPrefix n) =
    (ForgetEnrichment.to (Complex A) N) at H
  exact H

/-- 概要：左の境界データの apex 頂点の対象は標準余錐の指定対象。
方針：最初の三角形の等式を対応する頂点で評価する。
規約：追加の選択を使わない。使われ方：残差の端点の型の移送。 -/
lemma dgModuleConeBoundary_left_apex {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    (spanBoundaryLeftZeroData (sliceUnderUncurry b)).obj (spanApex n) = (ForgetEnrichment.to
      (Complex A) (moduleCone A D f)) := by
  have H := congrArg (fun s : SimplexData A (RightModule A D) 2 => s.obj (2 : Fin 3))
    (dgModuleConeBoundary_left_triangle A D f b hb)
  change (spanBoundaryLeftZeroData (sliceUnderUncurry b)).obj (spanApex n) =
    (ForgetEnrichment.to (Complex A) (moduleCone A D f)) at H
  exact H

/-- 概要：左の境界データの span 辺の成分は指定された鎖写像の cochain。
方針：最初の三角形への単射の制限を二点成分で評価する。
規約：対象の等号の移送を異種等号に含める。使われ方：脚との残差合成の同定。 -/
lemma dgModuleConeBoundary_left_span_heq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    HEq ((spanBoundaryLeftZeroData (sliceUnderUncurry b)).edgeHom
      0 (spanSecondPrefix n) (spanSecondPrefix_pos n))
      ((cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val) := by
  have H := SimplexData.edgeHom_heq_of_pullback_eq _ _ (firstTriangleOrderHom (n + 1))
    (firstTriangleOrderHom_injective (n + 1)) (dgModuleConeBoundary_left_triangle A D f b hb)
    (0 : Fin 3) 1 (by decide) (spanSecondPrefix_pos n)
  exact H.trans (heq_of_eq (show
    (dgModuleConeLowerTriangle A D f).simplex.toSimplexData.edgeHom 0 1 (by decide) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val from rfl))

/-- 概要：左の境界データの inclusion 辺の成分は指定された鎖写像の cochain。
方針：最初の三角形への単射の制限を二点成分で評価する。
規約：対象の等号の移送を異種等号に含める。使われ方：脚との残差合成の同定。 -/
lemma dgModuleConeBoundary_left_inclusion_heq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    HEq ((spanBoundaryLeftZeroData (sliceUnderUncurry b)).edgeHom
      (spanSecondPrefix n) (spanApex n) (spanSecondPrefix_lt_apex n))
      ((cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (moduleConeInr A D f))).val) := by
  have H := SimplexData.edgeHom_heq_of_pullback_eq _ _ (firstTriangleOrderHom (n + 1))
    (firstTriangleOrderHom_injective (n + 1)) (dgModuleConeBoundary_left_triangle A D f b hb)
    (1 : Fin 3) 2 (by decide) (spanSecondPrefix_lt_apex n)
  exact H.trans (heq_of_eq (show
    (dgModuleConeLowerTriangle A D f).simplex.toSimplexData.edgeHom 1 2 (by decide) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (moduleConeInr A D f))).val from rfl))

/-- 概要：左の境界データの diagonal 辺の成分は指定された鎖写像の cochain。
方針：最初の三角形への単射の制限を二点成分で評価する。
規約：対象の等号の移送を異種等号に含める。使われ方：脚との残差合成の同定。 -/
lemma dgModuleConeBoundary_left_diagonal_heq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    HEq ((spanBoundaryLeftZeroData (sliceUnderUncurry b)).edgeHom 0 (spanApex n) (spanApex_pos n))
      ((0 : GradedHom A (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A)
        (moduleCone A D f)) 0)) := by
  have H := SimplexData.edgeHom_heq_of_pullback_eq _ _ (firstTriangleOrderHom (n + 1))
    (firstTriangleOrderHom_injective (n + 1)) (dgModuleConeBoundary_left_triangle A D f b hb)
    (0 : Fin 3) 2 (by decide) (spanApex_pos n)
  exact H.trans (heq_of_eq (show
    (dgModuleConeLowerTriangle A D f).simplex.toSimplexData.edgeHom 0 2 (by decide) =
      (0 : GradedHom A (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A)
        (moduleCone A D f)) 0) from rfl))

/-- 概要：左の境界データの三点成分は指定された標準余錐のホモトピー。
方針：最初の三角形への単射の制限を三点成分で評価する。
規約：次数は −1。使われ方：三角形側の残差合成の同定。 -/
lemma dgModuleConeBoundary_left_homotopy_heq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    HEq ((spanBoundaryLeftZeroData (sliceUnderUncurry b)).tripleHom
      0 (spanSecondPrefix n) (spanApex n)
      (spanSecondPrefix_pos n) (spanSecondPrefix_lt_apex n))
      (moduleConeInlElement A D f) := by
  have H := SimplexData.tripleHom_heq_of_pullback_eq _ _ (firstTriangleOrderHom (n + 1))
    (firstTriangleOrderHom_injective (n + 1)) (dgModuleConeBoundary_left_triangle A D f b hb)
    (0 : Fin 3) 1 2 (by decide) (by decide)
    (spanSecondPrefix_pos n) (spanSecondPrefix_lt_apex n)
  exact H.trans (heq_of_eq (show
    (dgModuleConeLowerTriangle A D f).simplex.toSimplexData.tripleHom
      0 1 2 (by decide) (by decide) =
      moduleConeInlElement A D f from rfl))

/-- 概要：右の境界データの A 頂点の対象は標準余錐の指定対象。
方針：最初の三角形の等式を対応する頂点で評価する。
規約：追加の選択を使わない。使われ方：残差の端点の型の移送。 -/
lemma dgModuleConeBoundary_right_A {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    (spanBoundaryRightZeroData (sliceUnderUncurry b)).obj 0 = (ForgetEnrichment.to (Complex A)
      M) := by
  have H := congrArg (fun s : SimplexData A (RightModule A D) 2 => s.obj (0 : Fin 3))
    (dgModuleConeBoundary_right_triangle A D f b hb)
  change (spanBoundaryRightZeroData (sliceUnderUncurry b)).obj 0 = (ForgetEnrichment.to
    (Complex A) M) at H
  exact H

/-- 概要：右の境界データの C 頂点の対象は標準余錐の指定対象。
方針：最初の三角形の等式を対応する頂点で評価する。
規約：追加の選択を使わない。使われ方：残差の端点の型の移送。 -/
lemma dgModuleConeBoundary_right_C {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    (spanBoundaryRightZeroData (sliceUnderUncurry b)).obj (spanSecondPrefix n) = zeroModule A D
      := by
  have H := congrArg (fun s : SimplexData A (RightModule A D) 2 => s.obj (1 : Fin 3))
    (dgModuleConeBoundary_right_triangle A D f b hb)
  change (spanBoundaryRightZeroData (sliceUnderUncurry b)).obj (spanSecondPrefix n) =
    zeroModule A D at H
  exact H

/-- 概要：右の境界データの apex 頂点の対象は標準余錐の指定対象。
方針：最初の三角形の等式を対応する頂点で評価する。
規約：追加の選択を使わない。使われ方：残差の端点の型の移送。 -/
lemma dgModuleConeBoundary_right_apex {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    (spanBoundaryRightZeroData (sliceUnderUncurry b)).obj (spanApex n) = (ForgetEnrichment.to
      (Complex A) (moduleCone A D f)) := by
  have H := congrArg (fun s : SimplexData A (RightModule A D) 2 => s.obj (2 : Fin 3))
    (dgModuleConeBoundary_right_triangle A D f b hb)
  change (spanBoundaryRightZeroData (sliceUnderUncurry b)).obj (spanApex n) =
    (ForgetEnrichment.to (Complex A) (moduleCone A D f)) at H
  exact H

/-- 概要：右の境界データの span 辺の成分は指定された鎖写像の cochain。
方針：最初の三角形への単射の制限を二点成分で評価する。
規約：対象の等号の移送を異種等号に含める。使われ方：脚との残差合成の同定。 -/
lemma dgModuleConeBoundary_right_span_heq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    HEq ((spanBoundaryRightZeroData (sliceUnderUncurry b)).edgeHom
      0 (spanSecondPrefix n) (spanSecondPrefix_pos n))
      ((0 : GradedHom A (ForgetEnrichment.to (Complex A) M) (zeroModule A D) 0)) := by
  have H := SimplexData.edgeHom_heq_of_pullback_eq _ _ (firstTriangleOrderHom (n + 1))
    (firstTriangleOrderHom_injective (n + 1)) (dgModuleConeBoundary_right_triangle A D f b hb)
    (0 : Fin 3) 1 (by decide) (spanSecondPrefix_pos n)
  exact H.trans (heq_of_eq (show
    (dgModuleConeUpperTriangle A D f).simplex.toSimplexData.edgeHom 0 1 (by decide) =
      (0 : GradedHom A (ForgetEnrichment.to (Complex A) M) (zeroModule A D) 0) from rfl))

/-- 概要：右の境界データの inclusion 辺の成分は指定された鎖写像の cochain。
方針：最初の三角形への単射の制限を二点成分で評価する。
規約：対象の等号の移送を異種等号に含める。使われ方：脚との残差合成の同定。 -/
lemma dgModuleConeBoundary_right_inclusion_heq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    HEq ((spanBoundaryRightZeroData (sliceUnderUncurry b)).edgeHom
      (spanSecondPrefix n) (spanApex n) (spanSecondPrefix_lt_apex n))
      ((0 : GradedHom A (zeroModule A D) (ForgetEnrichment.to (Complex A) (moduleCone A D f))
        0)) := by
  have H := SimplexData.edgeHom_heq_of_pullback_eq _ _ (firstTriangleOrderHom (n + 1))
    (firstTriangleOrderHom_injective (n + 1)) (dgModuleConeBoundary_right_triangle A D f b hb)
    (1 : Fin 3) 2 (by decide) (spanSecondPrefix_lt_apex n)
  exact H.trans (heq_of_eq (show
    (dgModuleConeUpperTriangle A D f).simplex.toSimplexData.edgeHom 1 2 (by decide) =
      (0 : GradedHom A (zeroModule A D) (ForgetEnrichment.to (Complex A) (moduleCone A D f)) 0)
        from rfl))

/-- 概要：右の境界データの diagonal 辺の成分は指定された鎖写像の cochain。
方針：最初の三角形への単射の制限を二点成分で評価する。
規約：対象の等号の移送を異種等号に含める。使われ方：脚との残差合成の同定。 -/
lemma dgModuleConeBoundary_right_diagonal_heq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    HEq ((spanBoundaryRightZeroData (sliceUnderUncurry b)).edgeHom 0 (spanApex n) (spanApex_pos n))
      ((0 : GradedHom A (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A)
        (moduleCone A D f)) 0)) := by
  have H := SimplexData.edgeHom_heq_of_pullback_eq _ _ (firstTriangleOrderHom (n + 1))
    (firstTriangleOrderHom_injective (n + 1)) (dgModuleConeBoundary_right_triangle A D f b hb)
    (0 : Fin 3) 2 (by decide) (spanApex_pos n)
  exact H.trans (heq_of_eq (show
    (dgModuleConeUpperTriangle A D f).simplex.toSimplexData.edgeHom 0 2 (by decide) =
      (0 : GradedHom A (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A)
        (moduleCone A D f)) 0) from rfl))

/-- 概要：右の境界データの三点成分は指定された標準余錐のホモトピー。
方針：最初の三角形への単射の制限を三点成分で評価する。
規約：次数は −1。使われ方：三角形側の残差合成の同定。 -/
lemma dgModuleConeBoundary_right_homotopy_heq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    HEq ((spanBoundaryRightZeroData (sliceUnderUncurry b)).tripleHom
      0 (spanSecondPrefix n) (spanApex n)
      (spanSecondPrefix_pos n) (spanSecondPrefix_lt_apex n))
      ((0 : GradedHom A (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A)
        (moduleCone A D f)) (-1))) := by
  have H := SimplexData.tripleHom_heq_of_pullback_eq _ _ (firstTriangleOrderHom (n + 1))
    (firstTriangleOrderHom_injective (n + 1)) (dgModuleConeBoundary_right_triangle A D f b hb)
    (0 : Fin 3) 1 2 (by decide) (by decide)
    (spanSecondPrefix_pos n) (spanSecondPrefix_lt_apex n)
  exact H.trans (heq_of_eq (show
    (dgModuleConeUpperTriangle A D f).simplex.toSimplexData.tripleHom
      0 1 2 (by decide) (by decide) =
      (0 : GradedHom A (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A)
        (moduleCone A D f)) (-1)) from rfl))

end SerrePositivity.InfinityCategories
