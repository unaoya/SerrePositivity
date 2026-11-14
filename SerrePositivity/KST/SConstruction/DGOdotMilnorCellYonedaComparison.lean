module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorCompletionComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGModuleExtensionYonedaNerveIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGFullSubcategoryNerve
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulPostcomposition
public import SerrePositivity.KST.SConstruction.PerfectDGExtension
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorCoherence
public import SerrePositivity.DifferentialGraded.Perfect.Compact.Enhancement
public import SerrePositivity.DifferentialGraded.Category.Tensor

/-!
概要：同じ resolved cell 商包含について、実 Perf 延長と元 Yoneda の全自然性を回収する。
方針：D の全 Hom 自然な延長比較を、充満忠実な Perf 包含から戻す。
規約：固定 ν との最終比較や実 S 長方形の存在をここでは仮定しない。
使われ方：完備化後の商辺と固定 ν の cell 商辺の自然性照合。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "T" => DGCategoryCellResolution.Source R (DGOdotGluing R d)
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGOdotGluing R d)
  (dgQuotientImage R (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d)))
local notation "Q" => DGQuotient.QuotientObject (T) (P)
local notation "j" => DGQuotient.inclusion R (T) (P)

/-- 概要：同じ cell 商包含後の元商 Yoneda を共通宇宙の始域で表す。
方針：同じ対象宇宙の下降と実商包含を合成する。
規約：元の商包含を保持する。使われ方：全自然性比較の終点。 -/
def dgOdotMilnorCellYonedaTarget :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, u + 1, u + 1} R (T)).comp
    ((j).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (Q)))

/-- 概要：同じ比較終点を全加群へ含めると元商の Yoneda を回収する。
方針：元の dg 関手の結合則と D の包含式を使用する。
規約：全 dg 関手の等号。使われ方：Perf 包含からの反映。 -/
lemma dgOdotMilnorCellYonedaTarget_inclusion :
    (dgOdotMilnorCellYonedaTarget R d).comp (perfectDGModuleInclusion R (Q) Set.univ) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, u + 1, u + 1} R (T)).comp ((j).comp (dgYoneda R (Q))) := by
  unfold dgOdotMilnorCellYonedaTarget
  rw [strictDGFunctor_comp_assoc, strictDGFunctor_comp_assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda_inclusion]

/-- 概要：同じ cell Yoneda に同じ商包含の実 Perf 延長を施す。
方針：二つの実 dg 関手を合成する。規約：全 Hom 作用を保持する。
使われ方：全自然性比較の始点。 -/
def dgOdotMilnorCellYonedaExtension :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYonedaCommonFunctor R (T)).comp (perfectDGExtension R (T) (Q) (j))

/-- 概要：比較始点を全加群へ含めると元の graph 延長を回収する。
方針：同じ dg 合成の結合則と Perf 延長の包含則を使用する。
規約：全 dg 関手の等号。使われ方：D の全加群比較の適用。 -/
lemma dgOdotMilnorCellYonedaExtension_inclusion :
    (dgOdotMilnorCellYonedaExtension R d).comp (perfectDGModuleInclusion R (Q) Set.univ) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, u + 1, u + 1} R (T)).comp
        ((dgYoneda R (T)).comp (dgModuleExtension R (T) (Q) (j))) := by
  unfold dgOdotMilnorCellYonedaExtension _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYonedaCommonFunctor
  simp only [strictDGFunctor_comp_assoc]
  rw [perfectDGExtension_inclusion,
    ← strictDGFunctor_comp_assoc (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (T))
      (perfectDGModuleInclusion R (T) Set.univ) (dgModuleExtension R (T) (Q) (j)),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda_inclusion]

/-- 概要：同じ二つの Perf 関手は全加群への包含後に指定同型を持つ。
方針：D の全 Hom 自然な延長・Yoneda 比較をそのまま使用する。
規約：対象別同型で代用しない。使われ方：充満忠実包含からの反映。 -/
def dgOdotMilnorCellYonedaModuleComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorCellYonedaExtension R d) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGModuleInclusion R (Q) Set.univ))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorCellYonedaTarget R d) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGModuleInclusion R (Q) Set.univ)) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp,
    dgOdotMilnorCellYonedaExtension_inclusion, dgOdotMilnorCellYonedaTarget_inclusion]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionYonedaNerveIso R (T) (Q) (j)

/-- 概要：同じ cell 商包含による実 Perf 延長は元商の Yoneda と全関手圏で比較できる。
方針：全加群上の指定比較を同じ Perf の充満忠実包含で反映する。
規約：対象別の representable 同型だけに弱めない。
使われ方：resolved 完備化射と固定 ν の商辺の全自然性。 -/
def dgOdotMilnorCellYonedaComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorCellYonedaExtension R d))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorCellYonedaTarget R d)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSubcategoryInclusionNerve_isFullyFaithful R (RightModule R (Q))
    (modulePerfectProjectiveOver R (Q) Set.univ)).preimageFunctorIso
      (dgOdotMilnorCellYonedaModuleComparison R d)

end SerrePositivity.KST.SConstruction
