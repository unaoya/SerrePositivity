module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorIdentityNuSquare
public import SerrePositivity.KST.SConstruction.DGKNativeNuNaturality
public import SerrePositivity.KST.SConstruction.PerfectLaxIdempotent
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.LaxComparisonEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Pretriangulated
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SmallPerfectDGPretriangulated
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedQuasiEquivalenceForward

/-!
概要：恒等 Hom gluing の同じ三頂点を native 完備圏と固定 ν 値で比較する。
方針：元の小 Perf 包絡と実 gluing の完備性・前三角性を既存供給から得る。
規約：同じ対象と二辺を保ち、恒等 lax 差との比較を仮定で代用しない。
使われ方：実右零化面の列認証に必要な native／固定 ν 二辺の全自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "B" => DGOdotGluing R d
local notation "Q" => DGQuotient.QuotientObject (DGCategoryCellResolution.Source R (B))
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (B)
    (dgQuotientImage R (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d))))
local notation "C" => DGOdotMilnorIdentityBase R d
local notation "L" => DGOdotMilnorIdentityGluing R d
local notation "D" => DGOdotMilnorIdentityDifference R d
local notation "I" => DGFunctor.id (C)
local notation "M" => dgHomGluingBimodule R (C) (C) (C) (I) (I)
local notation "F" => dgHomGluingConeFunctor R (C) (C) (C) (I) (I)

/-- 概要：同じ恒等二脚の小 Perf 基底の dg 前三角性。
方針：元の小代表系から同じ包絡への準同値で輸送する。
規約：全 Perf の Small 性を要求しない。使われ方：native 対角の完全性。 -/
lemma dgOdotMilnorIdentityBase_pretriangulated : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (C) := by
  letI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectDGModuleOver_isDGPretriangulated R (Q) Set.univ
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isDGPretriangulated_of_quasiEquivalence_forward R _ _
    (dgSmallPerfectEnvelopeSmallInclusion R (Q) Empty (dgSmallPerfectBaseFamily R (Q)))
    (dgSmallPerfectEnvelopeSmallInclusion_quasiEquivalence R _ _ _)

/-- 概要：元の全 cone 像を含む差の小模型の dg 前三角性。
方針：同じ基底上の小代表系から実包絡への準同値で輸送する。
規約：cone の実対象を保つ。使われ方：native 差の完全性。 -/
lemma dgOdotMilnorIdentityDifference_pretriangulated : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (D) := by
  letI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectDGModuleOver_isDGPretriangulated R (C) Set.univ
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isDGPretriangulated_of_quasiEquivalence_forward R _ _
    (dgSmallPerfectEnvelopeSmallInclusion R (C) (L) (F).obj)
    (dgSmallPerfectEnvelopeSmallInclusion_quasiEquivalence R _ _ _)

/-- 概要：恒等 Hom gluing 自身の dg 前三角性。
方針：同じ小 Perf 二因子の前三角性を D の gluing 供給へ渡す。
規約：Perf(gluing) に置換しない。使われ方：native 中央と固定 ν の比較。 -/
lemma dgOdotMilnorIdentityGluing_pretriangulated : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (L) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluing_isDGPretriangulated R (C) (C) (M)
    (dgOdotMilnorIdentityBase_pretriangulated R d)
    (dgOdotMilnorIdentityBase_pretriangulated R d)

/-- 概要：同じ恒等二脚の小 Perf 基底は coherent 冪等完備。
方針：元の実 Perf 完備性を同じ評価同値で戻す。
規約：resolved 商自体の完備性を要求しない。使われ方：右面の native 左端。 -/
lemma dgOdotMilnorIdentityBase_complete : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (C)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectModuleNerve_isIdempotentComplete R (Q)).of_equivalence
    (dgSmallPerfectEnvelopeNerveEquivalence R (Q) Empty (dgSmallPerfectBaseFamily R (Q))).symm

/-- 概要：元 cone 全像の同じ小模型は coherent 冪等完備。
方針：同じ実 Perf 評価同値で D の完備性を戻す。
規約：差関手の像を変えない。使われ方：右面の native 終域。 -/
lemma dgOdotMilnorIdentityDifference_complete : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (D)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectModuleNerve_isIdempotentComplete R (C)).of_equivalence
    (dgSmallPerfectEnvelopeNerveEquivalence R (C) (L) (F).obj).symm

/-- 概要：同じ恒等 Hom gluing の native 中央は coherent 冪等完備。
方針：D2 の実導来 lax 比較と元二因子の完備性を使用する。
規約：恒等 lax 差への全比較は別工程。使われ方：native 中央の ν 比較同値。 -/
lemma dgOdotMilnorIdentityGluing_complete : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (L)) := by
  have hC := (dgOdotMilnorIdentityBase_complete R d).ulift.{u + 1}
  have hL := perfectLaxPullback_isIdempotentComplete
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, u + 1, u + 1} R (C))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R (C) (C) (M)) hC hC
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isIdempotentComplete_of_ulift
    (hL.of_equivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence R (C) (C) (M)).symm)

local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (C) := dgOdotMilnorIdentityBase_pretriangulated R d
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (L) := dgOdotMilnorIdentityGluing_pretriangulated R d
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (D) := dgOdotMilnorIdentityDifference_pretriangulated R d

/-- 概要：同じ native 基底と固定 ν 基底値の指定比較は同値。
方針：同じ Yoneda 比較へ実完備性を渡す。規約：全単体の同じ比較。
使われ方：恒等対角の始域比較。 -/
lemma dgOdotMilnorIdentityBase_nu_equivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (dgKNativeValueComparison R (C)) :=
  dgKNativeValueComparison_isQCatEquivalence R (C) (dgOdotMilnorIdentityBase_complete R d)

/-- 概要：同じ native Hom gluing と固定 ν 中央値の指定比較は同値。
方針：元 gluing の実完備性で Yoneda 比較を認証する。
規約：元の中央圏を保持する。使われ方：右面の中央頂点比較。 -/
lemma dgOdotMilnorIdentityGluing_nu_equivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (dgKNativeValueComparison R (L)) :=
  dgKNativeValueComparison_isQCatEquivalence R (L) (dgOdotMilnorIdentityGluing_complete R d)

/-- 概要：同じ native cone 小模型と固定 ν 終域値の指定比較は同値。
方針：実像模型の完備性を同じ Yoneda 比較へ渡す。
規約：差の全像を保持する。使われ方：右面の終域比較。 -/
lemma dgOdotMilnorIdentityDifference_nu_equivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (dgKNativeValueComparison R (D)) :=
  @dgKNativeValueComparison_isQCatEquivalence R _ (D) _ _
    (dgOdotMilnorIdentityDifference_pretriangulated R d)
    (dgOdotMilnorIdentityDifference_complete R d)

/-- 概要：同じ strict 対角と固定 ν 辺を全関手同型で比較する。
方針：既存の同じ native／ν 自然性を特殊化する。
規約：対象別比較で代用しない。使われ方：実右面の包含境界比較。 -/
def dgOdotMilnorIdentityDiagonal_nu_comparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (dgKNativeValueComparison R (C) ≫
      (dgKInputNuMap R (dgOdotMilnorIdentityDiagonalInputMap R d)).hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorIdentityDiagonal R d) ≫ dgKNativeValueComparison R (L)) :=
  dgKNativeNuNaturality R (C) (L) (dgOdotMilnorIdentityDiagonal R d)

/-- 概要：同じ実 cone 差と固定 ν 辺を全関手同型で比較する。
方針：元の差関手を同じ native／ν 自然性へ渡す。
規約：元の実 Hom 作用を保持する。使われ方：実右面の差境界比較。 -/
def dgOdotMilnorIdentityDifference_nu_comparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (dgKNativeValueComparison R (L) ≫
      (dgKInputNuMap R (dgOdotMilnorIdentityDifferenceInputMap R d)).hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorIdentityDifference R d) ≫ dgKNativeValueComparison R (D)) :=
  @dgKNativeNuNaturality R _ (L) (D) _ _
    (dgOdotMilnorIdentityGluing_pretriangulated R d) _ _
    (dgOdotMilnorIdentityDifference_pretriangulated R d) (dgOdotMilnorIdentityDifference R d)

end SerrePositivity.KST.SConstruction
