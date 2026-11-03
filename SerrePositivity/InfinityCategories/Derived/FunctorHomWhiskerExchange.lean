module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomGeneral
public import SerrePositivity.InfinityCategories.Core.CatInfinity.FunctorIsoWhiskerExchange
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyRepresentative
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
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
