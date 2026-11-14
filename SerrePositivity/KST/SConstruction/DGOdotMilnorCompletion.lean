module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNativePerfect
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGPerfectYonedaIdempotentCompletion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveUniverseLift

/-!
概要：D-21 の実 Yoneda 完備化を同じ Milnor resolved 商と固定 ν 値へ特殊化する。
方針：対象宇宙の上げ下げと元の Perf 評価同値で実完備化を輸送する。
規約：商を選び直さず、完備化射を strict 局所化と仮定しない。
使われ方：dgOdotMilnorPerfectSequence の c・hc を具体的証拠で充足する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGOdotGluing R d) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnor_isDGPretriangulated R d
local notation "Q" => DGQuotient.QuotientObject
  (DGCategoryCellResolution.Source R (DGOdotGluing R d))
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGOdotGluing R d)
    (dgQuotientImage R (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d))))
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (Q) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotient_isDGPretriangulated R (DGOdotGluing R d) _

/-- 概要：同じ native 商から D-21 の共通宇宙始域への同値。
方針：同じ対象を持ち上げる実準同値を使う。規約：対象の分解を変更しない。
使われ方：実 Yoneda 完備化の始域の照合。 -/
def dgOdotMilnorResolvedLiftEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeResolvedQuotient R d).obj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, u + 1} (Q))) :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.dgNerve_map_isQCatEquivalence_of_quasiEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, u + 1, u + 1} R (Q))
    (dgKUniverseLiftUp_quasiEquivalence R (Q))).choose

/-- 概要：固定 resolved 入力の Perf と元の native 商の Perf の実同値。
方針：対象宇宙を下げる準同値の一回 Perf 延長を使う。
規約：同じ商包含の対象を保つ。使われ方：完備化終域の照合。 -/
def dgOdotMilnorResolvedPerfectDownEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R (dgOdotMilnorResolvedInput R d)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R (Q))) := by
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, u + 1, u + 1} R (Q)
  letI : (quasiEquivalencePerfectExtension R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, u + 1} (Q))
      (Q) F).IsEquivalence :=
    (quasiEquivalencePerfectEquivalence R _ _ F
      (dgKUniverseLiftDown_quasiEquivalence R (Q))).isEquivalence_functor
  exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.dgNerve_map_isQCatEquivalence_of_quasiEquivalence
    (perfectDGExtension R _ _ F) (perfectDGExtension_quasiEquivalence R _ _ F)).choose

/-- 概要：元商の実 Perf から同じ固定 ν 値への指定同値。
方針：同じ対象宇宙比較の逆と presented Perf 評価の逆を合成する。
規約：別の完備化模型で置換しない。使われ方：D-21 の終域輸送。 -/
def dgOdotMilnorResolvedPerfectValueEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R (Q)))
    (dgKInputStableValue R (dgOdotMilnorResolvedInput R d)).obj :=
  (dgOdotMilnorResolvedPerfectDownEquivalence R d).symm.trans
    (presentedPerfectDGQCatEvaluationEquivalence R (dgOdotMilnorResolvedInput R d)).symm

/-- 概要：元 native resolved 商から同じ固定 ν 値への実完備化射。
方針：D-21 の同じ Yoneda 射を始域・終域の指定同値で輸送する。
規約：完備化の存在を追加仮定にしない。使われ方：Cat^perf Milnor 列の c。 -/
def dgOdotMilnorCompletion : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeResolvedQuotient R d)
    (dgKInputStableValue R (dgOdotMilnorResolvedInput R d)) where
  hom := (dgOdotMilnorResolvedLiftEquivalence R d).hom ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYonedaInfinity R (Q) ≫ (dgOdotMilnorResolvedPerfectValueEquivalence R d).hom)
  isExact := by
    letI := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
      (dgOdotMilnorResolvedLiftEquivalence R d).isQCatEquivalence
    letI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYonedaInfinity_isExactFunctor R (Q)
    letI := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
      (dgOdotMilnorResolvedPerfectValueEquivalence R d).isQCatEquivalence
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _

/-- 概要：構成した同じ c は実際に冪等完備化。
方針：D-21 の充満忠実性・retract 表示を同じ二同値で輸送する。
規約：元の全 coherent 冪等完備性を保持する。使われ方：Cat^perf Milnor 列の hc。 -/
theorem dgOdotMilnorCompletion_isIdempotentCompletion :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion (dgOdotMilnorCompletion R d).hom := by
  let U := dgOdotMilnorResolvedLiftEquivalence R d
  let V := dgOdotMilnorResolvedPerfectValueEquivalence R d
  have hY := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYonedaInfinity_isIdempotentCompletion R (Q)
  refine ⟨dgKInputStableValue_isIdempotentComplete R _,
    U.isQCatEquivalence.isFullyFaithful.comp
      (hY.2.1.comp V.isQCatEquivalence.isFullyFaithful), ?_⟩
  intro z
  obtain ⟨x, hx⟩ := hY.2.2 (V.inv.app (Opposite.op ⦋0⦌) z)
  refine ⟨U.inv.app (Opposite.op ⦋0⦌) x, ?_⟩
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf.of_iso (V.invHomIso.app z).symm).trans
    ((hx.map V.hom).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf.of_iso
      (((U.invHomIso.app x).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYonedaInfinity R (Q))).map V.hom).symm))

end SerrePositivity.KST.SConstruction
