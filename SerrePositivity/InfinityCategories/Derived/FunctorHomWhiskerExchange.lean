module
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoWhiskerExchange
public import SerrePositivity.InfinityCategories.F1B.HomotopyRepresentative
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering
/-!
概要：可逆とは限らない実関手変換と、前後合成による交換則を証明する。
方針：元の二つの実辺の積の正方形を、全関手空間の合成へ写す。
規約：変換の可逆性を要求しない。使われ方：augmentation と raw factor の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
/-- 元の全関手変換の前後合成は、可逆性なしに同じ指定交換正方形を満たす。 -/
lemma functorHom_whisker_exchange {X Y Z : SSet.{u}} [Quasicategory Y] [Quasicategory Z]
    {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z} (e : FunctorHom f₀ f₁) (d : FunctorHom g₀ g₁) :
    (hoFunctor.map ((ihom X).map g₀)).toFunctor.map e ≫
      (hoFunctor.map ((pre f₁).app Z)).toFunctor.map d =
    (hoFunctor.map ((pre f₀).app Z)).toFunctor.map d ≫
      (hoFunctor.map ((ihom X).map g₁)).toFunctor.map e := by
  obtain ⟨ee, rfl⟩ := homotopyCategory_homMk_surjective (functorVertex f₀) (functorVertex f₁) e
  obtain ⟨dd, rfl⟩ := homotopyCategory_homMk_surjective (functorVertex g₀) (functorVertex g₁) d
  change Truncated.HomotopyCategory.homMk (ee.map ((truncation 2).map ((ihom X).map g₀))) ≫
      Truncated.HomotopyCategory.homMk (dd.map ((truncation 2).map ((pre f₁).app Z))) =
    Truncated.HomotopyCategory.homMk (dd.map ((truncation 2).map ((pre f₀).app Z))) ≫
      Truncated.HomotopyCategory.homMk (ee.map ((truncation 2).map ((ihom X).map g₁)))
  have h := congrArg
    (fun k ↦ (Truncated.mapHomotopyCategory
      ((truncation 2).map (MonoidalClosed.comp X Y Z))).map k)
    (Truncated.HomotopyCategory.BinaryProduct.square ee dd)
  simp only [Functor.map_comp, Truncated.mapHomotopyCategory_homMk] at h
  exact F2.homMk_square_of_edge_eq _ _ _ _
    (ee.map ((truncation 2).map ((ihom X).map g₀)))
    (dd.map ((truncation 2).map ((pre f₁).app Z)))
    (dd.map ((truncation 2).map ((pre f₀).app Z)))
    (ee.map ((truncation 2).map ((ihom X).map g₁))) h
    (F2.functorComposition_post_edge _ _) (F2.functorComposition_pre_edge _ _)
    (F2.functorComposition_pre_edge _ _) (F2.functorComposition_post_edge _ _)
/-- 実ホモトピーと指定関手同型の交換は、元の全関手圏の変換の等式を与える。 -/
lemma homotopy_postcomp_iso_exchange {X Y Z : SSet.{u}} [Quasicategory Y] [Quasicategory Z]
    {f₀ f₁ : X ⟶ Y} (H : SSet.Homotopy f₀ f₁)
    {g₀ g₁ : Y ⟶ Z} (d : FunctorIso g₀ g₁) :
    Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp H g₀)) ≫
      (d.precomp f₁).hom =
    (d.precomp f₀).hom ≫ Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp H g₁)) := by
  simp only [functorHomotopyPostcomp_hom, F2.functorIso_precomp_hom]
  exact functorHom_whisker_exchange
    (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)) d.hom
end SerrePositivity.InfinityCategories
