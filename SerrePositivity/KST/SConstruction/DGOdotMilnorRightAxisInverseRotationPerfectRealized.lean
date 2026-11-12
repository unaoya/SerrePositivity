module
public import SerrePositivity.KST.SConstruction.DGPerfectComparisonInverseRotationPerfectRealized
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisInverseRotationYoneda
public import SerrePositivity.KST.SConstruction.DGKNativeValueComparison

/-!
概要：元 Milnor 実逆回転の二段 realization 全比較を同じ resolved 商の固定 ν 値へ運ぶ。
方針：同じ実 Perf 全族と元 Yoneda 全比較を充満忠実包含から反映し、元 ν 評価で写す。
規約：元 cell 始域・resolved 射影・元全比較を保持する。
使われ方：共通 S 長方形の実右面と上指定二単体の全接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "P" => DGCategoryCellResolution.Source R (DGOdotGluing R d)
local notation "Q" => DGQuotient.QuotientObject (P)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGOdotGluing R d)
    (dgQuotientImage R (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d))))
local notation "F" => dgOdotMilnorRightAxisQuotientSource R d
local notation "G" => dgOdotMilnorRightAxisQuotientTarget R d
local notation "τ" => dgOdotMilnorRightAxisQuotientComparison R d

local notation "q" => dgOdotMilnorResolvedInclusion R d
local notation "i" => perfectDGModuleInclusion R (Q) Set.univ

/-- 概要：同じ元 Milnor 実逆回転の二段全 realization を strict Perf 値で保持。
方針：元二 Perf 関手と元全比較を同じ持ち上げへ代入する。
規約：同じ実対象・全 Hom を保持。使われ方：固定 ν 比較の元始域。 -/
abbrev dgOdotMilnorRightAxisInverseRotationPerfectRealizedFamily :=
  dgPerfectComparisonInverseRotationPerfectRealizedFamily R (Q) (F) (G) (τ)
local notation "PF" => dgOdotMilnorRightAxisInverseRotationPerfectRealizedFamily R d

/-- 概要：元 Milnor Perf 全族の全加群表示は元二段全 realization そのもの。
方針：元二段の全包含回収を特殊化する。
規約：全関手の等号。使われ方：元全比較と上指定二単体の反映。 -/
lemma dgOdotMilnorRightAxisInverseRotationPerfectRealizedFamily_underlying :
    dgPerfectModuleUnderlying R (Q) (PF) =
      dgOdotMilnorRightAxisInverseRotationRealizedFamily R d :=
  dgPerfectComparisonInverseRotationPerfectRealizedFamily_underlying R (Q) (F) (G) (τ)

/-- 概要：元 Milnor 全比較を同じ Perf 全包含の両端へ正規化する。
方針：同じ二段実像回収と元 Yoneda 包含則で端点だけを移す。
規約：元全比較の値を保持。使われ方：Perf 全比較の反映。 -/
def dgOdotMilnorRightAxisInverseRotationPerfectModuleYonedaComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (PF) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (i))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((q).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (Q))) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (i)) := by
  let ha := (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
    ((dgOdotMilnorRightAxisInverseRotationPerfectRealizedFamily_underlying R d).symm.trans
      (dgPerfectModuleUnderlying_inclusion R (Q) (PF)))).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (PF) (i))
  have hb : (q).comp (dgYoneda R (Q)) =
      ((q).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (Q))).comp (i) :=
    (congrArg (fun k => (q).comp k) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda_inclusion R (Q))).symm.trans
      (strictDGFunctor_comp_assoc (q) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (Q)) (i)).symm
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (dgOdotMilnorRightAxisInverseRotationYonedaComparison R d) ha
    ((congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map hb).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp _ (i)))

/-- 概要：元二段全 realization と同じ resolved 射影 Yoneda の全 Perf 比較。
方針：元全加群比較を同じ充満忠実な Perf 包含で反映する。
規約：元 cell 始域・元商射影を保持。使われ方：固定 ν への同じ実全比較。 -/
def dgOdotMilnorRightAxisInverseRotationPerfectYonedaComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (PF)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((q).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (Q)))) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSubcategoryInclusionNerve_isFullyFaithful R (RightModule R (Q))
    (modulePerfectProjectiveOver R (Q) Set.univ)).preimageFunctorIso
      (dgOdotMilnorRightAxisInverseRotationPerfectModuleYonedaComparison R d)

/-- 概要：元 Milnor 全 Perf 比較は包含後に同じ元全加群比較を回収する。
方針：元充満忠実包含の逆像回収則を使用する。
規約：同型の等号を保持。使われ方：元上指定二単体を同じ全比較に保つ。 -/
lemma dgOdotMilnorRightAxisInverseRotationPerfectYonedaComparison_postcomp :
    (dgOdotMilnorRightAxisInverseRotationPerfectYonedaComparison R d).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (i)) =
      dgOdotMilnorRightAxisInverseRotationPerfectModuleYonedaComparison R d :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSubcategoryInclusionNerve_isFullyFaithful R (RightModule R (Q))
    (modulePerfectProjectiveOver R (Q) Set.univ)).preimageFunctorIso_postcomp _

local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGOdotGluing R d) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnor_isDGPretriangulated R d
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (Q) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotient_isDGPretriangulated R (DGOdotGluing R d)
    (dgQuotientImage R (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d)))

/-- 概要：元実逆回転二段 realization は同じ resolved 射影の固定 ν 値と全比較される。
方針：元 Perf 全比較を同じ元 ν 評価同値で後合成する。
規約：同じ元 resolved 射影・元 cell 始域を保持。
使われ方：実右面全比較と固定 ν の上指定二単体を接続する終端。 -/
def dgOdotMilnorRightAxisInverseRotationRealizedNuComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (PF) ≫ (dgKNativePerfectValueEquivalence R (Q)).hom)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (q) ≫ dgKNativeValueComparison R (Q)) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    ((dgOdotMilnorRightAxisInverseRotationPerfectYonedaComparison R d).postcomp
      (dgKNativePerfectValueEquivalence R (Q)).hom) rfl
    ((congrArg (fun m => m ≫ (dgKNativePerfectValueEquivalence R (Q)).hom)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (q) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (Q)))).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun m => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (q) ≫ m)
            (dgKNativeValueComparison_eq R (Q)).symm)))
end SerrePositivity.KST.SConstruction
