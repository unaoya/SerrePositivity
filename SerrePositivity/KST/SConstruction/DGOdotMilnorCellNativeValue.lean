module
public import SerrePositivity.KST.SConstruction.DGKNativeValueComparison
public import SerrePositivity.KST.SConstruction.DGOdotMilnorSourceNativePerfect

/-!
概要：元 cell 始域・同じ核・cell gluing を固定 ν 値へ実同値で比較する。
方針：構成済みの native 完備性を同じ Yoneda 比較の同値判定へ渡す。
規約：順方向は同じ実 Yoneda 比較であり、S 内の逆 dg 関手を要求しない。
使われ方：零化面の native 証拠を固定 ν 像へ照合する三つの頂点比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => DGSmallPerfectBase R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.source d))
local notation "T" => DGCategoryCellResolution.Source R (A)
local notation "B" => DGOdotGluing R d
local notation "K" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernel R (B)
  (dgQuotientImage R (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d)))

/-- 概要：元始域の cell 分解から同じ固定 ν 値への指定同値。
方針：同じ実 Yoneda 比較に native 完備性を適用する。
規約：増大屋根の元の cell 始域を保持する。使われ方：始域比較面の左頂点。 -/
def dgOdotMilnorSourceCellNativeValueEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (T))
    (dgKInputStableValue R (dgOdotMilnorSourceCellInput R d)).obj := by
  letI : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (A) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorSource_isDGPretriangulated R d
  letI : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (T) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R (A)
  exact (dgKNativeValueComparison_isQCatEquivalence R (T)
    (dgOdotMilnorSourceCell_complete R d)).choose

/-- 概要：同じ thick 平坦核から同じ固定 ν 値への指定同値。
方針：Milnor 条件から得た native 完備性と前三角性を使用する。
規約：thick 核の全対象を保つ。使われ方：元始域回収と実零化面の左頂点。 -/
def dgOdotMilnorSourceKernelNativeValueEquivalence (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (K))
      (dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)).obj := by
  letI : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (K) := dgOdotMilnorSourceKernel_isDGPretriangulated R d h
  exact (dgKNativeValueComparison_isQCatEquivalence R (K)
    (dgOdotMilnorSourceKernel_complete R d h)).choose

/-- 概要：元 gluing の cell 分解から同じ固定 ν 値への指定同値。
方針：実 gluing の完備性と cell 増大の同値を使用する。
規約：商射影の始域を保持する。使われ方：実零化面の中央頂点。 -/
def dgOdotMilnorCellMiddleNativeValueEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGCategoryCellResolution.Source R (B)))
      (dgKInputStableValue R (dgOdotMilnorCellInput R d)).obj := by
  letI : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (B) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnor_isDGPretriangulated R d
  letI : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGCategoryCellResolution.Source R (B)) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R (B)
  exact (dgKNativeValueComparison_isQCatEquivalence R
    (DGCategoryCellResolution.Source R (B)) (dgOdotMilnorCellMiddle_complete R d)).choose

end SerrePositivity.KST.SConstruction
