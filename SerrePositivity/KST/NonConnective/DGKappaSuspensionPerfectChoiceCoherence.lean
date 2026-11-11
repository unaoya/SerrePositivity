module
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionPerfectChoiceEquivalence
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionChoiceCoherence

/-!
概要：元の実商の選択比較の恒等・合成を、同じ Yoneda 完備化後の Perf へ反映する。
方針：指定 Yoneda 比較を合成し、完備化に沿う全関手圏の充満忠実性を使う。
規約：固定 κ・元の実商・元の Yoneda を保持する。全 dg 入力作用は別工程。
使われ方：K-7 d4 の選択比較と下降の整合、任意高次パラメータへの制限。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective

variable (R : Type u) [CommRing R] (A : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I J K : DGKappaConeInput R A κ)
  (P : DGKappaPerfectInput R A I) (Q : DGKappaPerfectInput R A J)
  (T : DGKappaPerfectInput R A K)
local notation "δI" => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (dgKappaSuspensionKInput R A I))
local notation "δK" => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (dgKappaSuspensionKInput R A K))

/-- 同じ実商の自己比較を保つ Perf 比較は、元の Perf 恒等関手と同型。 -/
def dgKappaSuspensionPerfectChoice_selfIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKappaSuspensionPerfectChoiceEquivalence R A I I P P).hom (𝟙 _) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.pre_isFullyFaithful_general δI
    (dgKappaRawSuspensionYoneda_isIdempotentCompletion R A I)).preimageVertexIso
  have e := (dgKappaSuspensionPerfectChoiceEquivalence_yonedaIso R A I I P P) ≪≫
    (dgKappaSuspensionChoiceMap_selfIso R A I P).postcomp δI
  simpa only [Category.id_comp, Category.comp_id, dgKappaSuspensionChoiceEquivalence] using! e

/-- 三選択の同じ Perf 比較は、元の実商の合成比較と整合する。 -/
def dgKappaSuspensionPerfectChoice_compIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((dgKappaSuspensionPerfectChoiceEquivalence R A I J P Q).hom ≫
      (dgKappaSuspensionPerfectChoiceEquivalence R A J K Q T).hom)
      (dgKappaSuspensionPerfectChoiceEquivalence R A I K P T).hom := by
  let F := (dgKappaSuspensionPerfectChoiceEquivalence R A I J P Q).hom
  let G := (dgKappaSuspensionPerfectChoiceEquivalence R A J K Q T).hom
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.pre_isFullyFaithful_general δI
    (dgKappaRawSuspensionYoneda_isIdempotentCompletion R A I)).preimageVertexIso
  have e₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (δI ≫ (F ≫ G))
      (dgKappaSuspensionChoiceMap R A I J P Q ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (dgKappaSuspensionKInput R A J)) ≫ G)) := by
    simpa only [Category.assoc, F, dgKappaSuspensionChoiceEquivalence] using!
      (dgKappaSuspensionPerfectChoiceEquivalence_yonedaIso R A I J P Q).postcomp G
  have e₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (dgKappaSuspensionChoiceMap R A I J P Q ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (dgKappaSuspensionKInput R A J)) ≫ G))
      (dgKappaSuspensionChoiceMap R A I J P Q ≫
        (dgKappaSuspensionChoiceMap R A J K Q T ≫ δK)) := by
    simpa only [G, dgKappaSuspensionChoiceEquivalence] using!
      (dgKappaSuspensionPerfectChoiceEquivalence_yonedaIso R A J K Q T).precomp
        (dgKappaSuspensionChoiceMap R A I J P Q)
  have e₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (dgKappaSuspensionChoiceMap R A I J P Q ≫
        (dgKappaSuspensionChoiceMap R A J K Q T ≫ δK))
      (dgKappaSuspensionChoiceMap R A I K P T ≫ δK) := by
    simpa only [Category.assoc] using!
      (dgKappaSuspensionChoiceMap_compIso R A I J K P Q T).postcomp δK
  have e₃ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKappaSuspensionChoiceMap R A I K P T ≫ δK)
      (δI ≫ (dgKappaSuspensionPerfectChoiceEquivalence R A I K P T).hom) := by
    simpa only [dgKappaSuspensionChoiceEquivalence] using!
      (dgKappaSuspensionPerfectChoiceEquivalence_yonedaIso R A I K P T).symm
  exact e₀ ≪≫ e₁ ≪≫ e₂ ≪≫ e₃

/-- 任意の Perf 高次パラメータ族でも、元の指定合成比較を使う。 -/
def dgKappaSuspensionPerfectChoiceParameterIso {S : SSet.{max (u + 1) v}}
    (a : S ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory R (dgKappaSuspensionKInput R A I)) :=
  (dgKappaSuspensionPerfectChoice_compIso R A I J K P Q T).precomp a

/-- 同じ比較の再制限は、元の族の合成に対する比較そのもの。 -/
theorem dgKappaSuspensionPerfectChoiceParameterIso_precomp {S U : SSet.{max (u + 1) v}}
    (a : S ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory R (dgKappaSuspensionKInput R A I)) (r : U ⟶ S) :
    (dgKappaSuspensionPerfectChoiceParameterIso R A I J K P Q T a).precomp r =
      dgKappaSuspensionPerfectChoiceParameterIso R A I J K P Q T (r ≫ a) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp _ _ _

end SerrePositivity.KST.NonConnective
