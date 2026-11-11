module
public import SerrePositivity.KST.SConstruction.DGPerfectRealizationPerfect
public import SerrePositivity.KST.SConstruction.DGPerfectRealizationYonedaNative
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPerfectYoneda
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFullSubcategoryNerve
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulNormalizedIsoRecovery

/-!
概要：同じ strict Perf realization の元 Yoneda 評価を全 Perf 関手同型として保持する。
方針：元全加群評価の両端を厳密に回収し、充満忠実な Perf 包含で反映する。
規約：元右単位評価と元全 Hom 自然性を変更しない。
使われ方：二段 realization を指定小包絡の固定 ν 値比較へ照合する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C E : Type (u + 1))
  [DGCategory R C] [Small.{u} C] [DGCategory R E] [Small.{u} E]
  (J : DGFunctor R C (PerfectDGModule R E))
local notation "VP" => dgPerfectRealizationPerfect R C E J
local notation "V" => dgPerfectRealization R C E J
local notation "Y" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R C
local notation "i" => perfectDGModuleInclusion R E Set.univ

/-- 概要：元 strict Perf Yoneda 評価の全加群表示は元 realization そのもの。
方針：元 Perf 制限の包含回収と元 Yoneda の包含回収を合成する。
規約：全 dg 関手の厳密等号。使われ方：全比較の始域正規化。 -/
lemma dgPerfectRealizationPerfectYoneda_underlying :
    dgPerfectModuleUnderlying R E ((Y).comp (VP)) = (dgYoneda R C).comp (V) := by
  have hY := (dgPerfectModuleUnderlying_inclusion R C (Y)).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda_inclusion R C)
  exact (dgPerfectRealizationPerfect_underlying R C E J (Y)).trans
    (congrArg (fun F => F.comp (V)) hY)

/-- 概要：元全代表評価を、同じ Perf 包含の両端を持つ全比較へ正規化する。
方針：元実全関手等号と native nerve の合成回収を使う。
規約：元評価同型の値を保持。使われ方：充満忠実包含による反映。 -/
def dgPerfectRealizationPerfectYonedaModuleComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (VP)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (i))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map J ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (i)) := by
  have ha := (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
    ((dgPerfectRealizationPerfectYoneda_underlying R C E J).symm.trans
      (dgPerfectModuleUnderlying_inclusion R E ((Y).comp (VP))))).trans
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp ((Y).comp (VP)) (i)).trans
          (congrArg (fun F => F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (i)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (Y) (VP))))
  have hb := (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectModuleUnderlying_inclusion R E J)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp J (i))
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (dgPerfectRealizationYonedaNerveComparison R E C J) ha hb

/-- 概要：同じ strict Perf realization の Yoneda 評価は元 J と全関手同型。
方針：元全加群評価を同じ充満忠実 Perf 包含で反映する。
規約：元代表評価の全自然性を保持。使われ方：小包絡の指定 ν 値評価への接続。 -/
def dgPerfectRealizationPerfectYonedaComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (VP)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map J) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSubcategoryInclusionNerve_isFullyFaithful R (RightModule R E)
    (modulePerfectProjectiveOver R E Set.univ)).preimageFunctorIso
      (dgPerfectRealizationPerfectYonedaModuleComparison R C E J)

/-- 概要：同じ Perf 全比較は包含後に元全代表評価を厳密に回収する。
方針：元充満忠実包含の指定逆像回収を使う。
規約：全関手同型の等号。使われ方：元指定二単体の評価比較の保持。 -/
lemma dgPerfectRealizationPerfectYonedaComparison_postcomp :
    (dgPerfectRealizationPerfectYonedaComparison R C E J).postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (i)) =
      dgPerfectRealizationPerfectYonedaModuleComparison R C E J :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSubcategoryInclusionNerve_isFullyFaithful R (RightModule R E)
    (modulePerfectProjectiveOver R E Set.univ)).preimageFunctorIso_postcomp _

end SerrePositivity.KST.SConstruction
