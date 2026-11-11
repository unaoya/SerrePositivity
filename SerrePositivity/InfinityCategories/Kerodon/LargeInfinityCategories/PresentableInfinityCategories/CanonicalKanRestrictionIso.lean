module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCanonicalRestrictionHom

/-!
概要：密度を保つ二つの関手の間の射の可逆性を制限で反映する。
方針：制限後の逆射を Hom 全単射で持ち上げ、両合成を同じ単射で検査する。
規約：全ての関手への制限の充満忠実性は仮定しない。
使われ方：専用反映候補の余単位の可逆性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：標準局所余錐を保つ関手間の射は制限後に可逆なら可逆。
方針：逆射と左右の逆の等式を元の Hom 全単射から回収する。
規約：元の指定射自体を判定する。
使われ方：密度による余単位の回収。 -/
lemma functorHom_isIso_of_canonicalRestriction
    {K A X : SSet.{u}} [Quasicategory K] [Quasicategory A] [Quasicategory X]
    (δ : K ⟶ A) {F G : A ⟶ X}
    (hF : ∀ a, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F a))
    (hG : ∀ a, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ G a))
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G)
    (hη : IsIso ((hoFunctor.map ((pre δ).app X)).toFunctor.map η)) : IsIso η := by
  let R := (hoFunctor.map ((pre δ).app X)).toFunctor
  have hi : IsIso (R.map η) := hη
  obtain ⟨θ, hθ⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonicalHomMap_bijective δ G hG F).surjective (inv (R.map η))
  have hleft : η ≫ θ = 𝟙 _ := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonicalHomMap_bijective δ F hF F).injective
    change R.map (η ≫ θ) = R.map (𝟙 _)
    rw [Functor.map_comp, hθ, IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
  have hright : θ ≫ η = 𝟙 _ := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonicalHomMap_bijective δ G hG G).injective
    change R.map (θ ≫ η) = R.map (𝟙 _)
    rw [Functor.map_comp, hθ, IsIso.inv_hom_id, CategoryTheory.Functor.map_id]
  exact ⟨θ, hleft, hright⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
