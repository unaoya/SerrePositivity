module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallShapePresentable
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallShapeTensor
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.ComparisonWithTopologicalSpaces.FiniteInternalHomContinuity

/-!
概要：μ-small な形状からの内部 Hom は、μ-filtered な通常の余極限を保つ。
方針：各次数を K × Δ[n] からの Hom と比較し、同じ形状の μ-presentability を使う。
規約：非可算正則 μ、元の strict な単体集合図式。coherent な極限交換自体はまだ結論しない。
使われ方：weighted 極限の各写像空間の μ-filtered 連続性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 元の μ-small な形状からの内部 Hom は、同じ μ-filtered strict 余極限を保つ。 -/
lemma smallInternalHom_preservesCardinalFilteredColimits {μ : Cardinal.{u}} [Fact μ.IsRegular]
    (hμ : Cardinal.aleph0 < μ) (K : SSet.{u}) (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ K)
    (I : Type u) [SmallCategory I] [IsCardinalFiltered I μ] :
    PreservesColimitsOfShape I (ihom K) := by
  apply preservesColimitsOfShape_of_evaluation
  intro n
  have hn : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ (K ⊗ stdSimplex.obj n.unop) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaSmall_tensor hμ hK (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_of_finite hμ.le _)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallShape_isCardinalPresentable hμ (K ⊗ stdSimplex.obj n.unop) hn
  have : PreservesColimitsOfShape I
      (coyoneda.obj (op (K ⊗ stdSimplex.obj n.unop))) :=
    preservesColimitsOfShape_of_isCardinalPresentable _ μ I
  exact preservesColimitsOfShape_of_natIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.ComparisonWithTopologicalSpaces.internalHomEvaluationIso K n).symm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
