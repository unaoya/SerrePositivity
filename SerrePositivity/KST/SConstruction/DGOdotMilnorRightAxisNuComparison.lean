module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisResolvedLift
public import SerrePositivity.KST.SConstruction.DGOdotMilnorCellNativeValue
public import SerrePositivity.KST.SConstruction.DGKNativeNuNaturality
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeNativeProperties
public import SerrePositivity.KST.SConstruction.PerfectLaxIdempotent
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.LaxComparisonEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Pretriangulated

/-!
概要：同じ実中央 dg 射の native 全辺を保存済み固定 ν 辺へ比較する。
方針：元二像小模型・逆回転小基底の前三角性と完備性を保って ν 自然性を適用する。
規約：D2 の元終域上の全 lax 比較や LT 長方形認証を仮定充足とは数えない。
使われ方：D2 非依存の固定 ν 中央射比較と同じ実 S 長方形の頂点準備。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants

variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "B" => DGOdotGluing R d
local notation "P" => DGCategoryCellResolution.Source R (B)
local notation "Q" => DGQuotient.QuotientObject (P)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (B)
    (dgQuotientImage R (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d))))
local notation "T" => DGPerfectComparisonBase R (Q)
  (dgOdotMilnorRightAxisQuotientSource R d) (dgOdotMilnorRightAxisQuotientTarget R d)
local notation "U" => DGOdotMilnorRightAxisBase R d
local notation "L" => DGOdotMilnorRightAxisTarget R d
local notation "M" => dgHomGluingBimodule R (U) (U) (U) (DGFunctor.id (U)) (DGFunctor.id (U))

/-- 概要：元二実像を含む同じ比較小模型の前三角性。
方針：同じ小 Perf 包絡の性質を使用する。規約：元二実像を保持。
使われ方：逆回転終域の実基底の構成。 -/
lemma dgOdotMilnorRightAxisComparisonBase_pretriangulated : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (T) :=
  dgSmallPerfectEnvelope_pretriangulated R (Q) _ _

/-- 概要：同じ逆回転の cone 全像小基底の前三角性。
方針：同じ全実像包絡の性質を使用する。規約：cone 実像を保持。
使われ方：native 中央射終域の完全性。 -/
lemma dgOdotMilnorRightAxisBase_pretriangulated : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (U) :=
  dgSmallPerfectEnvelope_pretriangulated R (T) _ _

/-- 概要：同じ逆回転の cone 全像小基底の coherent 完備性。
方針：同じ実評価同値で Perf の完備性を戻す。規約：元基底の完備性は不要。
使われ方：native 中央射終域の完備性。 -/
lemma dgOdotMilnorRightAxisBase_complete : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (U)) :=
  dgSmallPerfectEnvelope_complete R (T) _ _

/-- 概要：同じ恒等 Hom gluing の実中央射終域は前三角。
方針：元二因子の前三角性を既存 gluing 定理へ渡す。
規約：別の Perf 圏に置換しない。使われ方：固定 ν の実辺の比較。 -/
lemma dgOdotMilnorRightAxisTarget_pretriangulated : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (L) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluing_isDGPretriangulated R (U) (U) (M)
    (dgOdotMilnorRightAxisBase_pretriangulated R d)
    (dgOdotMilnorRightAxisBase_pretriangulated R d)

/-- 概要：同じ実中央射終域の native nerve は coherent 冪等完備。
方針：既存の実導来係数 lax 同値で両因子の完備性を戻す。
規約：元終域上の新しい D2 全比較とは区別する。使われ方：ν 比較同値。 -/
lemma dgOdotMilnorRightAxisTarget_complete : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (L)) := by
  have hU := (dgOdotMilnorRightAxisBase_complete R d).ulift.{u + 1}
  have hL := perfectLaxPullback_isIdempotentComplete
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, u + 1, u + 1} R (U))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R (U) (U) (M)) hU hU
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isIdempotentComplete_of_ulift
    (hL.of_equivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence R (U) (U) (M)).symm)

local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (B) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnor_isDGPretriangulated R d
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (P) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R (B)

/-- 概要：同じ実中央射終域から同じ固定 ν 入力値への指定同値。
方針：元 native 完備性を同じ Yoneda 比較へ適用する。
規約：保存済み実 S 頂点を保持。使われ方：固定 ν 長方形の中央下頂点。 -/
def dgOdotMilnorRightAxisTargetNativeValueEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (L)) (dgKInputStableValue R (dgOdotMilnorRightAxisInput R d)).obj :=
  (@dgKNativeValueComparison_isQCatEquivalence R _ (L) _ _
    (dgOdotMilnorRightAxisTarget_pretriangulated R d)
    (dgOdotMilnorRightAxisTarget_complete R d)).choose

/-- 概要：保存済み実中央辺の native 像と同じ固定 ν 辺の全比較。
方針：元 dg 関手に同じ ν 自然性を適用する。
規約：同じ実中央射を保持。使われ方：実長方形中央辺の固定 ν 認証。 -/
def dgOdotMilnorRightAxisNuComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotMilnorCellMiddleNativeValueEquivalence R d).hom ≫
      (dgOdotMilnorRightAxisExactMap R d).hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorRightAxisLift R d) ≫
      (dgOdotMilnorRightAxisTargetNativeValueEquivalence R d).hom) :=
  @dgKNativeNuNaturality R _ (P) (L) _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R (B)) _ _
    (dgOdotMilnorRightAxisTarget_pretriangulated R d) (dgOdotMilnorRightAxisLift R d)

/-- 概要：同じ固定 ν 始域から元 native 中央射を経る指定屋根。
方針：元 cell 比較同値の逆と同じ native 中央射・終域比較を合成する。
規約：厳密 dg 逆増大は不要。使われ方：固定 ν の中央射の実 native 表示。 -/
def dgOdotMilnorRightAxisNuNativeRoof :
    (dgKInputStableValue R (dgOdotMilnorCellInput R d)).obj ⟶
      (dgKInputStableValue R (dgOdotMilnorRightAxisInput R d)).obj :=
  (dgOdotMilnorCellMiddleNativeValueEquivalence R d).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorRightAxisLift R d) ≫
      (dgOdotMilnorRightAxisTargetNativeValueEquivalence R d).hom

/-- 概要：固定 ν の実中央辺は同じ native 屋根と全関手同型。
方針：同じ中央射自然性を元 cell 同値の逆で前合成し、指定余単位を貼る。
規約：元の保存済み実 S 辺を保持。使われ方：全長方形中央辺の指定比較。 -/
def dgOdotMilnorRightAxisNuNativeRoof_comparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (dgOdotMilnorRightAxisNuNativeRoof R d) (dgOdotMilnorRightAxisExactMap R d).hom := by
  let e := dgOdotMilnorCellMiddleNativeValueEquivalence R d
  let f := (dgOdotMilnorRightAxisExactMap R d).hom
  have a := (dgOdotMilnorRightAxisNuComparison R d).precomp e.inv
  have b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (e.inv ≫ (e.hom ≫ f)) f :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (e.invHomIso.postcomp f) (Category.assoc _ _ _) (Category.id_comp _)
  exact a.symm ≪≫ b

end SerrePositivity.KST.SConstruction
