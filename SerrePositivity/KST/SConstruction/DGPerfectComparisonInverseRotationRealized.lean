module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingInverseRotationRealizedNative
public import SerrePositivity.KST.SConstruction.DGPerfectComparisonHomGluing
public import SerrePositivity.KST.SConstruction.DGPerfectRealizationYonedaRestriction
public import SerrePositivity.KST.SConstruction.DGPerfectModuleUnderlyingComposition

/-!
概要：元二実像小模型の実逆回転全比較を元 Perf 値へ戻す。
方針：元実逆回転全比較を元 realization で後合成し同じ元代表評価を合成する。
規約：元始域・元二実像・元全 Hom と指定厳密逆を保持する。
使われ方：LT 実右面の合成全比較と指定上下二単体への接続。
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

/-- 概要：元実逆回転全 realization の元 Perf 加群値への二段評価族。
方針：同じ二実像小模型を二段とも使用する。
規約：元全関手を保持。使われ方：元入力上の実合成全比較の始域。 -/
def dgPerfectComparisonInverseRotationRealizedFamily : DGFunctor R P (RightModule R E) :=
  ((H).comp (Q)).comp (V)

/-- 概要：元実逆回転全 realization と元第二 Perf 値の全関手同型。
方針：同じ指定厳密逆全比較・元代表評価・全包含回収を合成する。
規約：対象別の同値や別の厳密代表へ置換しない。
使われ方：LT 実右面の全合成比較と固定 ν の指定二単体への接続。 -/
def dgPerfectComparisonInverseRotationRealizedNerveComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectComparisonInverseRotationRealizedFamily R E F G τ))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectModuleUnderlying R E G)) := by
  let e := dgIdentityHomGluingInverseRotationRealizedNerveComparison R (T) (F0) (G0) (a) (h)
  let eV := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (e.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (V)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp ((H).comp (Q)) (V)).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp ((G0).comp (dgYoneda R (T))) (V)).symm
  let eY := dgPerfectRealizationYonedaRestrictedNerveComparison R E (T) (J) (G0)
  have hg : (G0).comp (dgPerfectModuleUnderlying R E (J)) = dgPerfectModuleUnderlying R E G :=
    dgPerfectModuleUnderlying_comp_of_eq R E (G0) (J) G
      (dgSmallPerfectEnvelopeFunctorLift_inclusion R E (P ⊕ P) (family) G Sum.inr (fun _ => rfl))
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (eV.trans eY) rfl (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map hg)
end SerrePositivity.KST.SConstruction
