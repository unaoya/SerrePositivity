module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallShapePresentable
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallShapeTensor
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FiniteInternalHomContinuity

/-!
概要：μ-small な形状からの内部 Hom は、μ-filtered な通常の余極限を保つ。
方針：各次数を K × Δ[n] からの Hom と比較し、同じ形状の μ-presentability を使う。
規約：非可算正則 μ、元の strict な単体集合図式。coherent な極限交換自体はまだ結論しない。
使われ方：weighted 極限の各写像空間の μ-filtered 連続性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 元の μ-small な形状からの内部 Hom は、同じ μ-filtered strict 余極限を保つ。 -/
lemma smallInternalHom_preservesCardinalFilteredColimits {μ : Cardinal.{u}} [Fact μ.IsRegular]
    (hμ : Cardinal.aleph0 < μ) (K : SSet.{u}) (hK : IsKappaSmall μ K)
    (I : Type u) [SmallCategory I] [IsCardinalFiltered I μ] :
    PreservesColimitsOfShape I (ihom K) := by
  apply preservesColimitsOfShape_of_evaluation
  intro n
  have hn : IsKappaSmall μ (K ⊗ stdSimplex.obj n.unop) :=
    isKappaSmall_tensor hμ hK (isKappaSmall_of_finite hμ.le _)
  have := smallShape_isCardinalPresentable hμ (K ⊗ stdSimplex.obj n.unop) hn
  have : PreservesColimitsOfShape I
      (coyoneda.obj (op (K ⊗ stdSimplex.obj n.unop))) :=
    preservesColimitsOfShape_of_isCardinalPresentable _ μ I
  exact preservesColimitsOfShape_of_natIso (internalHomEvaluationIso K n).symm

end SerrePositivity.InfinityCategories.F2.Presentable
