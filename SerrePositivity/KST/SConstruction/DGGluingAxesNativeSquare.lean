module
public import SerrePositivity.KST.SConstruction.DGGluingAxesCommonCells
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGPretriangulatedYonedaExact
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.Pretriangulated

/-! # 元の dg gluing の実二軸押し出し四角形
概要：元の二軸二セルを共通宇宙で貼り、同じ Yoneda 像から実押し出し性を反映する。
方針：二つの実二単体の対角一致と、前三角 Yoneda の押し出し反映を使う。
規約：元の閉零二成分と二軸射を保持。使われ方：具体的二軸分解と K-10 c。
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
local notation "F" => DGFunctor.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown R G) (dgYoneda R G)
local notation "s" => dgGluingAxesRepresentableCofiberData R C D M zc hc zd hd X

/-- 元の二軸二セルを貼った、共通宇宙の実 dg nerve 四角形。 -/
def dgGluingAxesNativeSquare :
    (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) (max v w)}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R GG :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.desc
    (SSet.yonedaEquiv.symm (dgGluingAxesCommonUpperCell R C D M zc hc zd hd X))
    (SSet.yonedaEquiv.symm (dgGluingAxesCommonLowerCell R C D M zc hc zd hd X))
    (dgGluingAxesCommonCells_compatible R C D M zc hc zd hd X)

/-- 同じ実四角形の下側セルは、元の包含・射影を持つ同じ二単体。 -/
lemma dgGluingAxesNativeSquare_lower :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ dgGluingAxesNativeSquare R C D M zc hc zd hd X =
      SSet.yonedaEquiv.symm (dgGluingAxesCommonLowerCell R C D M zc hc zd hd X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inr_desc _ _ _

/-- 同じ実四角形の上側セルは、指定零対象を経由する同じ二単体。 -/
lemma dgGluingAxesNativeSquare_upper :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ dgGluingAxesNativeSquare R C D M zc hc zd hd X =
      SSet.yonedaEquiv.symm (dgGluingAxesCommonUpperCell R C D M zc hc zd hd X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inl_desc _ _ _

/-- 同じ実四角形の Yoneda 像は、元の四代表 cofiber 四角形そのもの。 -/
lemma dgGluingAxesNativeSquare_yoneda :
    dgGluingAxesNativeSquare R C D M zc hc zd hd X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (F) =
      dgGluingAxesRepresentableCofiberSquare R C D M zc hc zd hd X := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  · erw [← Category.assoc, dgGluingAxesNativeSquare_upper, SSet.yonedaEquiv_symm_comp]
    change (SSet.yonedaEquiv.symm
      ((dgGluingAxesCommonUpperCell R C D M zc hc zd hd X).map (F)) :
        (Δ[2] : SSet.{max (u + 1) (max v w)}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R G) = _
    erw [dgGluingAxesCommonUpperCell_yoneda]
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData.square_upper (s)).symm
  · erw [← Category.assoc, dgGluingAxesNativeSquare_lower, SSet.yonedaEquiv_symm_comp]
    change (SSet.yonedaEquiv.symm
      ((dgGluingAxesCommonLowerCell R C D M zc hc zd hd X).map (F)) :
        (Δ[2] : SSet.{max (u + 1) (max v w)}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R G) = _
    erw [dgGluingAxesCommonLowerCell_yoneda]
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData.square_lower (s)).symm

/-- 元の二圏の前三角性により、同じ二軸四角形は実 dg nerve の ∞ 押し出し。 -/
lemma dgGluingAxesNativeSquare_isPushout
    (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (dgGluingAxesNativeSquare R C D M zc hc zd hd X) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluing_isDGPretriangulated R C D M hC hD
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPretriangulatedYoneda_reflectsPushoutSquare R G
  rw [dgGluingAxesNativeSquare_yoneda]
  exact dgGluingAxesRepresentableCofiberSquare_isPushout R C D M zc hc zd hd X

end SerrePositivity.KST.SConstruction
