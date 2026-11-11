module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemConeRetraction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity

/-!
概要：元の全 coherent 冪等図式の添字 Idem は、任意の κ について κ-filtered。
方針：恒等図式の実余錐を、任意の元の図式に沿って制限する。
規約：試験図式を nerve 上の図式へ制限せず、元の全単体を保持。
使われ方：Indκ の冪等完備性と、元の Yoneda retract 閉包からの実比較。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

/-- 元の任意の全図式から Idem への写像は、同じ図式の実余錐を持つ。 -/
def idemShapeCocone {K : SSet.{u}} (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemShape.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone f :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 (Δ[0] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemConeRetraction, by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemConeRetraction_inl, Category.comp_id]⟩

/-- 全 Idem は、κ-small な任意の coherent 試験図式について κ-filtered。 -/
lemma idemShape_isKappaFiltered (κ : Cardinal.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemShape.{u} :=
  ⟨fun _ f ↦ ⟨idemShapeCocone f⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
