module
public import SerrePositivity.KST.SConstruction.DGGluingAxesNativeSquare
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGClosedZeroVertex

/-! # 元の二軸射を保つ実 dg nerve の cofiber 列
概要：貼り合わせた実四角形の二辺と零角を元の対象・閉射に厳密に同定する。
方針：上下セルの面を取り、同じ実閉零対象の宇宙移送を使う。
規約：一般の商・局所化 API は作らない。使われ方：具体的二軸分解と K-10 c。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory DifferentialGraded InfinityCategories
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (zc : C) (hc : IsZero (ForgetEnrichment.of (Complex R) zc))
  (zd : D) (hd : IsZero (ForgetEnrichment.of (Complex R) zd))
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "GG" => DGGluingAxesCommonUniverse R C D M
local notation "U" => dgGluingAxesCommonUp R C D M
local notation "A" => ForgetEnrichment.of (Complex R)
  (dgGluingRightAxisObject R C D M zc X.right)
local notation "Z" => ForgetEnrichment.of (Complex R)
  (dgGluingRightAxisObject R C D M zc zd)

/-- 同じ実四角形の下辺は、元の右軸包含の宇宙移送された実辺。 -/
lemma dgGluingAxesNativeSquare_bottom :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgGluingAxesNativeSquare R C D M zc hc zd hd X =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R GG
        ((U).onClosed.map (dgGluingAxisRightInclusion R C D M zc hc X))).edge := by
  erw [← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.cofiberSquareTriangle_bottomEdge, Category.assoc, dgGluingAxesNativeSquare_lower,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  apply congrArg SSet.yonedaEquiv.symm
  exact (dgSimplex_map_face _ (U) (2 : Fin 3)).trans
    ((congrArg (fun t => t.map (U))
      (dgGluingAxesCofiberLowerCell R C D M zc hc zd hd X).d₂).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_map R G (U) (dgGluingAxisRightInclusion R C D M zc hc X)))

/-- 同じ実四角形の右辺は、元の左軸射影の宇宙移送された実辺。 -/
lemma dgGluingAxesNativeSquare_right :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgGluingAxesNativeSquare R C D M zc hc zd hd X =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R GG
        ((U).onClosed.map (dgGluingAxisLeftProjection R C D M zd hd X))).edge := by
  erw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_rightEdge, Category.assoc, dgGluingAxesNativeSquare_lower,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  apply congrArg SSet.yonedaEquiv.symm
  exact (dgSimplex_map_face _ (U) (0 : Fin 3)).trans
    ((congrArg (fun t => t.map (U))
      (dgGluingAxesCofiberLowerCell R C D M zc hc zd hd X).d₀).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_map R G (U) (dgGluingAxisLeftProjection R C D M zd hd X)))

/-- 同じ実四角形の左辺は、指定 gluing 零対象への元の零射の実辺。 -/
lemma dgGluingAxesNativeSquare_left :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgGluingAxesNativeSquare R C D M zc hc zd hd X =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R GG ((U).onClosed.map (0 : A ⟶ Z))).edge := by
  erw [← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.cofiberSquareTriangle_leftEdge, Category.assoc, dgGluingAxesNativeSquare_upper,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  apply congrArg SSet.yonedaEquiv.symm
  exact (dgSimplex_map_face _ (U) (2 : Fin 3)).trans
    ((congrArg (fun t => t.map (U))
      (dgGluingAxesCofiberUpperCell R C D M zc hc zd hd X).d₂).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_map R G (U) (0 : A ⟶ Z)))

/-- 同じ実四角形の零角は、指定した元の gluing 零対象の宇宙移送。 -/
lemma dgGluingAxesNativeSquare_vertex01 :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgGluingAxesNativeSquare R C D M zc hc zd hd X) 0 1 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((U).obj (dgGluingRightAxisObject R C D M zc zd)) := by
  erw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftEdge_target, dgGluingAxesNativeSquare_left, Equiv.apply_symm_apply]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R GG ((U).onClosed.map (0 : A ⟶ Z))).tgt_eq

/-- 同じ指定零角は、元の共通宇宙 dg nerve で実零頂点。 -/
lemma dgGluingAxesNativeSquare_zero :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgGluingAxesNativeSquare R C D M zc hc zd hd X) 0 1) := by
  rw [dgGluingAxesNativeSquare_vertex01]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isZeroVertex_of_closed_isZero _
    ((U).onClosed.map_isZero (dgGluingClosedZero_isZero R C D M zc hc zd hd))

/-- 元の二軸射と指定零角を持つ、共通宇宙の実零角付き三角形。 -/
def dgGluingAxesNativeZeroTriangle : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R GG) where
  square := dgGluingAxesNativeSquare R C D M zc hc zd hd X
  zero_corner := dgGluingAxesNativeSquare_zero R C D M zc hc zd hd X

/-- 元の二圏が前三角的なら、元の同じ二軸列は実 ∞ cofiber 列となる。 -/
lemma dgGluingAxesNativeZeroTriangle_isCofiber
    (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence (dgGluingAxesNativeZeroTriangle R C D M zc hc zd hd X) :=
  dgGluingAxesNativeSquare_isPushout R C D M zc hc zd hd X hC hD

end SerrePositivity.KST.SConstruction
