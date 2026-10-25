module

public import SerrePositivity.InfinityCategories.F2.Ind.FiniteColimitFromPresentation
public import SerrePositivity.InfinityCategories.F2.Ind.FinitePosetDiagramPresentation

/-!
概要：元の有限半順序全図式の Ind 内での余極限存在。
方針：元の同じ全図式の単一 filtered 表示と全余極限族の補完を使う。
規約：Yoneda の有限余極限保存に必要な交換入力を明示する。
使われ方：Ind の押し出しと安定性への接続。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 明示交換入力のもとで、元の有限半順序全図式は Ind 内に余極限を持つ。 -/
lemma indFinitePoset_hasColimit (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    {P : Type u} [PartialOrder P] [Finite P] {C : SSet.{u}}
    [Quasicategory C] [HasFiniteColimits C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve P) ⟶ IndInfinity κ C) : HasColimit D :=
  ind_hasColimit_of_singleFilteredDiagramPresentation κ hκ hex D
    (indFinitePoset_has_singleFilteredDiagramPresentation κ D)

end SerrePositivity.InfinityCategories.F2.Ind
