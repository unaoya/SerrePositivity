module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport
public import SerrePositivity.KST.SConstruction.DGOdotMilnorOriginalLaxConeComparisonRequest
public import SerrePositivity.KST.SConstruction.DGKNativeValueComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SmallPerfectDGPretriangulated
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedQuasiEquivalenceForward

/-!
概要：元二脚の実 cone の終域評価を、同じ小 corner の Yoneda を保持して具体化する。
方針：元小模型の完備性と Yoneda 同値の逆を、同じ実包含評価へ合成する。
規約：元 corner 評価を追加入力にしない。lax 差との比較そのものは供給待ち。
使われ方：D2 の元二脚全 cone 比較に残す入力を、同じ実 cone 自然性へ限定する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.source
local notation "B" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.left
local notation "C" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.right
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.side
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower
local notation "q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper
local notation "J" => (DGSmallPerfectArrowTarget R (A) (B) (L)) ⊕
  (DGSmallPerfectArrowTarget R (A) (C) (G))
local notation "T" => dgSmallPerfectSquareCornerFamily R (A) (B) (C) (E) (L) (G) (p) (q)
local notation "V" => DGOdotCorner R d

/-- 概要：元小 corner の同じ実包含は元角代数 Perf との同値。
方針：元全像族を含む同じ小包絡の評価を使う。規約：全対象を保持。
使われ方：元角評価の指定順方向。 -/
def dgOdotMilnorCornerEnvelopeEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (V)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R (E))) :=
  dgSmallPerfectEnvelopeNerveEquivalence R (E) (J) (T)

/-- 概要：元小 corner 自身は dg 前三角圏。
方針：同じ実包絡への小代表系準同値で前三角性を輸送する。
規約：元 corner の置換なし。使われ方：native Yoneda 比較の認証。 -/
lemma dgOdotMilnorCorner_pretriangulated : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (V) := by
  letI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectDGModuleOver_isDGPretriangulated R (E) Set.univ
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isDGPretriangulated_of_quasiEquivalence_forward R _ _
    (dgSmallPerfectEnvelopeSmallInclusion R (E) (J) (T))
    (dgSmallPerfectEnvelopeSmallInclusion_quasiEquivalence R _ _ _)

/-- 概要：同じ元小 corner は coherent 冪等完備。
方針：元角代数 Perf の完備性を同じ実包含評価で戻す。
規約：完備性を追加仮定にしない。使われ方：同じ Yoneda の同値性。 -/
lemma dgOdotMilnorCorner_complete : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (V)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectModuleNerve_isIdempotentComplete R (E)).of_equivalence
    (dgOdotMilnorCornerEnvelopeEquivalence R d).symm

local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (V) := dgOdotMilnorCorner_pretriangulated R d

/-- 概要：元小 corner の同じ native Yoneda は実同値。
方針：native／ν 比較と固定 Perf 値比較の同値性から検出する。
規約：元の全 Yoneda を保持。使われ方：実 cone 終域評価の逆。 -/
lemma dgOdotMilnorCornerYoneda_equivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (V))) := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (V)) ≫
      (dgKNativePerfectValueEquivalence R (V)).hom) := by
    rw [← dgKNativeValueComparison_eq]
    exact dgKNativeValueComparison_isQCatEquivalence R (V) (dgOdotMilnorCorner_complete R d)
  exact (dgKNativePerfectValueEquivalence R (V)).isQCatEquivalence.cancel_right h

/-- 概要：実 cone の Perf 終域を同じ元角の固定 ν 値へ戻す指定同値。
方針：元小 corner の Yoneda 逆と、同じ実包含・元角評価を合成する。
規約：評価の存在を追加入力にしない。使われ方：D2 の全 cone 比較の終域。 -/
def dgOdotMilnorCornerEvaluation : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R (V)))
    (dgKInputStableValue R (dgOdotCornerInput R d)).obj :=
  (dgOdotMilnorCornerYoneda_equivalence R d).choose.symm.trans
    ((dgOdotMilnorCornerEnvelopeEquivalence R d).trans
      (dgOdotMilnorCornerPerfectValueEquivalence R d))

/-- 概要：指定評価は元小 corner の実包含評価を全 Yoneda 上で回収する。
方針：同じ Yoneda 同値の単位を元包含評価で後合成する。
規約：全関手同型。使われ方：D2 依頼型の cornerYoneda 欄を実証拠で満たす。 -/
def dgOdotMilnorCornerEvaluation_yoneda : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (V)) ≫ (dgOdotMilnorCornerEvaluation R d).hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgSmallPerfectSquareCornerInclusion R (A) (B) (C) (E) (L) (G) (p) (q)) ≫
      (dgOdotMilnorCornerPerfectValueEquivalence R d).hom) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    ((dgOdotMilnorCornerYoneda_equivalence R d).choose.homInvIso.postcomp
      ((dgOdotMilnorCornerEnvelopeEquivalence R d).hom ≫
        (dgOdotMilnorCornerPerfectValueEquivalence R d).hom))
    (Category.assoc _ _ _) (Category.id_comp _)

/-- 概要：元二脚の実 cone 全比較だけから、指定 corner 評価を持つ供給入力を満たす。
方針：構成済みの元角評価と全 Yoneda 回収を代入する。
規約：lax 比較と cone 全同型の存在は入力。使われ方：D2 の残供給の最小接続。 -/
def DGOdotMilnorOriginalLaxComparisonInput.withCone
    (v : DGOdotMilnorOriginalLaxComparisonInput R d)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((dgOdotMilnorNativeLaxComparison R d).hom ≫
        (v.gluing.hom ≫
          (exactLaxDifference (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d)).hom))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotTargetFunctor R d) ≫ (dgOdotMilnorCornerEvaluation R d).hom)) :
    DGOdotMilnorOriginalLaxConeComparisonInput R d where
  laxComparison := v
  cornerEvaluation := dgOdotMilnorCornerEvaluation R d
  cornerYoneda := dgOdotMilnorCornerEvaluation_yoneda R d
  cone := c
end SerrePositivity.KST.SConstruction
