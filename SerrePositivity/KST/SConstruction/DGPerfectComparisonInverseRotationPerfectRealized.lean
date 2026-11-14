module
public import SerrePositivity.KST.SConstruction.DGPerfectComparisonInverseRotationRealized
public import SerrePositivity.KST.SConstruction.DGIdentityInverseRotationPerfectRealization
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGFullSubcategoryNerve
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulNormalizedIsoRecovery

/-!
概要：元実逆回転の二段 realization を同じ全関手の strict Perf 値へ持ち上げる。
方針：二段の元実評価を Perf に制限し、元全比較を充満忠実包含で反映する。
規約：元全関手・指定厳密逆・実対象像を変更しない。
使われ方：同じ resolved 射影と固定 ν の全関手比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories MonoidalCategory
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  {P : Type (max (u + 1) v)} [DGCategory R P] [Small.{u} P]
  (F G : DGFunctor R P (PerfectDGModule R E))
  (τ : DGFunctorParamTrans R P (PerfectDGModule R E) (𝟙_ (Complex R)) F G)
local notation "T" => DGPerfectComparisonBase R E F G
local notation "family" => dgPerfectComparisonFamily R E F G
local notation "J" => dgSmallPerfectEnvelopeInclusion R E (P ⊕ P) (family)
local notation "V" => dgPerfectRealization R (T) E (J)
local notation "F0" => dgPerfectComparisonFirst R E F G
local notation "G0" => dgPerfectComparisonSecond R E F G
local notation "a" => dgPerfectComparisonMap R E F G τ
local notation "h" => dgPerfectComparisonMap_hom_naturality R E F G τ
local notation "H" => dgPerfectComparisonHomGluingFunctor R E F G τ
local notation "Q" => dgIdentityInverseRotationRealizedConeFamily R (T)

local notation "QP" => dgIdentityInverseRotationPerfectRealizedConeFamily R (T)
local notation "VP" => dgPerfectRealizationPerfect R (T) E (J)
local notation "i" => perfectDGModuleInclusion R E Set.univ

/-- 概要：元実逆回転二段 realization の同じ全実 Perf 族。
方針：元入力制限と二段の同じ tensor 評価の Perf 制限を合成する。
規約：同じ元小模型・全 Hom を保持。使われ方：固定 ν 全比較の始域。 -/
def dgPerfectComparisonInverseRotationPerfectRealizedFamily :
    DGFunctor R P (PerfectDGModule R E) := ((H).comp (QP)).comp (VP)

/-- 概要：元二段 Perf 全族は包含後に元の二段全 realization そのものを回収。
方針：同じ二段の包含回収と元入力の全合成則を使う。
規約：全 dg 関手の等号。使われ方：元 native 全比較の忠実な持ち上げ。 -/
lemma dgPerfectComparisonInverseRotationPerfectRealizedFamily_underlying :
    dgPerfectModuleUnderlying R E
      (dgPerfectComparisonInverseRotationPerfectRealizedFamily R E F G τ) =
      dgPerfectComparisonInverseRotationRealizedFamily R E F G τ := by
  change dgPerfectModuleUnderlying R E (((H).comp (QP)).comp (VP)) =
    ((H).comp (Q)).comp (V)
  rw [dgPerfectRealizationPerfect_underlying, ← dgPerfectModuleUnderlying_comp,
    dgIdentityInverseRotationPerfectRealizedConeFamily_underlying]

/-- 概要：同じ元二段全比較を元 Perf 全包含の両端に正規化する。
方針：元実対象像の全回収で端点だけを移す。
規約：元全比較の値を保持。使われ方：同じ元比較の Perf 反映。 -/
def dgPerfectComparisonInverseRotationPerfectModuleComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectComparisonInverseRotationPerfectRealizedFamily R E F G τ) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (i)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (i)) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (dgPerfectComparisonInverseRotationRealizedNerveComparison R E F G τ)
    ((congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      ((dgPerfectComparisonInverseRotationPerfectRealizedFamily_underlying R E F G τ).symm.trans
        (dgPerfectModuleUnderlying_inclusion R E
          (dgPerfectComparisonInverseRotationPerfectRealizedFamily R E F G τ)))).trans
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp _ (i)))
    ((congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectModuleUnderlying_inclusion R E G)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp G (i)))

/-- 概要：元二段実逆回転の全比較を同じ実 Perf nerve 内に保持する。
方針：元全加群比較を同じ充満忠実包含から持ち上げる。
規約：対象別同値を使わず全比較を反映。使われ方：固定 ν への元全比較。 -/
def dgPerfectComparisonInverseRotationPerfectNerveComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectComparisonInverseRotationPerfectRealizedFamily R E F G τ))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSubcategoryInclusionNerve_isFullyFaithful R (RightModule R E)
    (modulePerfectProjectiveOver R E Set.univ)).preimageFunctorIso
      (dgPerfectComparisonInverseRotationPerfectModuleComparison R E F G τ)

/-- 概要：Perf の元二段全比較は包含後に同じ元全加群比較を厳密回収する。
方針：充満忠実な元包含の逆像の回収則を使う。
規約：同型の等号を保持。使われ方：元上指定二単体の同じ全比較への接続。 -/
lemma dgPerfectComparisonInverseRotationPerfectNerveComparison_postcomp :
    (dgPerfectComparisonInverseRotationPerfectNerveComparison R E F G τ).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (i)) =
      dgPerfectComparisonInverseRotationPerfectModuleComparison R E F G τ :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSubcategoryInclusionNerve_isFullyFaithful R (RightModule R E)
    (modulePerfectProjectiveOver R E Set.univ)).preimageFunctorIso_postcomp _
end SerrePositivity.KST.SConstruction
