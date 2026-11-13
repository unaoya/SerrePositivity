module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeMappingDescent
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovPresentedSpaceLimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SquareFunctorTransport

/-!
概要：指定局所化上の実 cell 写像関手は、元の Postnikov 錐を極限錐へ送る。
方針：降下の比較二胞体を元の提示錐全体に前合成し、P-8 による極限性を輸送する。
規約：降下関手と表現可能 Hom はまだ同定せず、元の局所化錐の極限性とは区別する。
使われ方：E2-S (6) の全自然な Hom 比較を適用する実試験錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)

def postnikovCellLocalizationCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone
    ((SSet.uliftFunctor.{u + 2, u + 1}).map
      (nerveMap (postnikovInfinityCospan R B n hn) ≫ quasiIsoInfinityMap R) ≫
        multiplicativeCellMappingLocalizationFunctor R A) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (multiplicativeCellMappingLocalizationFunctor R A)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u + 1, u + 2} (postnikovInfinityCone R B n hn))

def postnikovCellLocalizationConeComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (postnikovCellLocalizationCone R A B n hn).val
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (multiplicativeCellMappingInfinityCoherent R A)
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u + 1, u + 2}
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone (postnikovInfinityPresentedCone R B n hn)))).val := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (multiplicativeCellMappingLocalizationTriangleIso R A)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u + 1, u + 2}
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone (postnikovInfinityPresentedCone R B n hn))).val
  have hv : (postnikovCellLocalizationCone R A B n hn).val =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u + 1, u + 2}
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone (postnikovInfinityPresentedCone R B n hn))).val ≫
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (quasiIsoInfinityMap R) ≫
        multiplicativeCellMappingLocalizationFunctor R A) := by
    change (((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso (nerve PostnikovInfinityShape.{u}) 0).inv ≫
      (SSet.uliftFunctor.{u + 2, u + 1}).map
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone (postnikovInfinityPresentedCone R B n hn)).val ≫
          quasiIsoInfinityMap R)) ≫ multiplicativeCellMappingLocalizationFunctor R A) =
      (((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso (nerve PostnikovInfinityShape.{u}) 0).inv ≫
        (SSet.uliftFunctor.{u + 2, u + 1}).map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone (postnikovInfinityPresentedCone R B n hn)).val) ≫ _)
    rw [Functor.map_comp]
    simp only [Category.assoc]
  rw [hv]
  exact e

lemma postnikovCellLocalizationCone_isLimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (postnikovCellLocalizationCone R A B n hn) :=
  (postnikovPresentedCellMappingImageCone_isLimit R A B n hn).of_functorIso
    (postnikovCellLocalizationConeComparison R A B n hn).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.4.1.29" (partial := component) "仮定：通常可換環 R 上の厳密非正次数の結合的 dg 代数 B、n≥0 と任意の dg cell 源（Lean が強い：この E₁ の dg 模型の場合）。結論：τ≤n+1 B の平方零 class の錐が擬同型 ∞ 局所化で実際に極限錐となり、実 cell 写像空間の錐も極限となる。摂動した左下の代数は τ≤n B に擬同型である（原典の隣接段の pullback の部分に一致）。塔全体の逆極限、零段の離散 Hom 同定、普遍 cotangent による導分の分類は含まれない。"] _root_.SerrePositivity.KST.LocalizingInvariants.DGAlgebra.postnikovCellLocalizationCone_isLimit
