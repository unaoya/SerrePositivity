module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemUniverse
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplittingExistence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LimitColimitOpposite
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseLimits
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InnerFibration

/-!
概要：元の coherent 冪等完備性は宇宙変更で保存・反映される。
方針：全 Idem の厳密な宇宙比較で元の図式を移し、同じ余極限の保存・反映を使う。
規約：大きい宇宙の任意の全 Idem 図式を扱い、固定された小さい図式だけに制限しない。
使われ方：前層圏を通す冪等完備な標的への延長の宇宙整合。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の coherent 冪等完備性は、任意の大きい宇宙への持ち上げで保存される。 -/
lemma IsIdempotentComplete.ulift {X : SSet.{u}} [Quasicategory X]
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete ((SSet.uliftFunctor.{v, u}).obj X) := by
  intro d
  let a := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemShapeUniverseIso.{u, v}).hom ≫ d
  let d₀ := (SSet.uliftFunctor.{v, u}).preimage a
  have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit ((SSet.uliftFunctor.{v, u}).map d₀) :=
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.hasColimit_iff_ulift d₀).mp (hX.hasColimit d₀)
  have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit a := by
    simpa only [d₀, Functor.map_preimage] using h₀
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit d :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanHasColimit_iff_restrict_of_isIso d (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemShapeUniverseIso.{u, v}).hom).mpr ha
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.strongSplitting_exists_of_hasColimit d hd

/-- 持ち上げた ∞ 圏の coherent 冪等完備性は、元の宇宙へ反映される。 -/
lemma isIdempotentComplete_of_ulift {X : SSet.{u}} [Quasicategory X]
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete ((SSet.uliftFunctor.{v, u}).obj X)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete X := by
  intro d
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemShapeUniverseIso.{u, v}
  let a := e.inv ≫ (SSet.uliftFunctor.{v, u}).map d
  have ha := hX.hasColimit a
  have h₀ := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanHasColimit_iff_restrict_of_isIso a e.hom).mp ha
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit ((SSet.uliftFunctor.{v, u}).map d) := by
    simpa only [a, e.hom_inv_id_assoc] using h₀
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.strongSplitting_exists_of_hasColimit d ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.hasColimit_iff_ulift d).mpr h₁)

/-- coherent な元の冪等完備性は、宇宙の持ち上げで保存・反映される。 -/
lemma isIdempotentComplete_iff_ulift (X : SSet.{u}) [Quasicategory X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete X ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete ((SSet.uliftFunctor.{v, u}).obj X) :=
  ⟨IsIdempotentComplete.ulift, isIdempotentComplete_of_ulift⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
