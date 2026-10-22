module

public import SerrePositivity.InfinityCategories.F2.Ind.IndLeftKanCanonical
public import SerrePositivity.InfinityCategories.F2.Ind.IndContinuousLeftKan

/-!
概要：構成済み左 Kan 延長は、元の指定 Indκ 頂点の同じ全密度余錐を余極限へ写す。
方針：元の標準 Kan 余錐を比較同値で制限し、同じ密度余錐の像の全射へ同定する。
規約：任意の κ-filtered 余極限の保存性は仮定しない。
使われ方：左 Kan 延長の κ-filtered 余極限保存性の密度入力。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {D : SSet.{u + 1}} [Quasicategory D]

/-- 元の指定左 Kan 延長は、元の全密度余錐を同じ指定値の native 余極限へ写す。 -/
lemma indLeftKanExtension_density_image_isColimit
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : IndInfinity κ C ⟶ D}
    (β : SSet.Homotopy F₀ (indYoneda κ C ≫ G))
    (hβ : IsLeftKanExtension (indYoneda κ C) F₀ G β) (v : (IndInfinity κ C) _⦋0⦌) :
    IsColimitCone (mapJoinCocone G (indVertexDensityCocone κ v)) := by
  have hc := (isColimitCone_iff_restrict_equivalentShape (indElementsLeftKanComparison κ v)
    (indElementsLeftKanComparison_isQCatEquivalence κ v)
    (leftKanCanonicalCocone (indYoneda κ C) G v)).mp
      (indLeftKanExtension_canonicalColimits κ β hβ v)
  exact (F2.isColimitCone_iff_of_cocone_val_eq _ _
    (indLeftKanCanonicalCocone_restrict_val κ G v)).mp hc

end SerrePositivity.InfinityCategories.F2.Ind
