module

public import SerrePositivity.InfinityCategories.F2.Ind.IndDensityKanCoconeMap
public import SerrePositivity.InfinityCategories.F2.Ind.EquivalentCoconeRestriction
public import SerrePositivity.InfinityCategories.Core.CatInfinity.CoconeValEquality
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCanonicalRestrictionHom

/-!
概要：元の小さい κ-filtered 余極限を保つ関手は、元の Yoneda に沿う標準左 Kan 条件を満たす。
方針：元の比較同値に制限した標準余錐を、同じ密度余錐の像へ厳密に同定する。
規約：保存性を元の native 余錐へ適用する。Yoneda の inner 性は仮定しない。
使われ方：保存関手の全部分圏からの実際の制限射の充満忠実性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {D : SSet.{u + 1}} (G : IndInfinity κ C ⟶ D) (v : (IndInfinity κ C) _⦋0⦌)

/-- 同じ小さい元の圏へ制限した標準 Kan 余錐の全射は、元の密度余錐の同じ像。 -/
lemma indLeftKanCanonicalCocone_restrict_val :
    ((leftKanCanonicalCocone (indYoneda κ C) G v).restrict
      (indElementsLeftKanComparison κ v)).val =
        (mapJoinCocone G (indVertexDensityCocone κ v)).val := by
  change joinMap (indElementsLeftKanComparison κ v) (𝟙 Δ[0]) ≫
    (slicePullbackCoconeMap (indYoneda κ C) (SSet.yonedaEquiv.symm v) ≫ G) = _
  rw [← Category.assoc, indElementsLeftKanComparison_coconeMap]
  rfl

/-- 元の κ-filtered 余極限を保つ関手の、同じ標準局所 Kan 余錐は余極限。 -/
lemma indContinuous_canonicalColimits [Fact κ.IsRegular] [Quasicategory D]
    (hG : PreservesSmallKappaFilteredColimits κ G) :
    IsColimitCone (leftKanCanonicalCocone (indYoneda κ C) G v) := by
  apply (isColimitCone_iff_restrict_equivalentShape (indElementsLeftKanComparison κ v)
    (indElementsLeftKanComparison_isQCatEquivalence κ v) _).mpr
  exact (F2.isColimitCone_iff_of_cocone_val_eq _ _
    (indLeftKanCanonicalCocone_restrict_val κ G v)).mpr
      (indVertexDensity_image_isColimit κ v G hG)

/-- 元の保存関手自身は、元の Yoneda による同じ制限の恒等単位付き左 Kan 拡張。 -/
lemma indContinuous_isLeftKanExtension [Fact κ.IsRegular] [Quasicategory D]
    (hG : PreservesSmallKappaFilteredColimits κ G) :
    IsLeftKanExtension (indYoneda κ C) (indYoneda κ C ≫ G) G
      (functorHomotopyRefl (indYoneda κ C ≫ G)) :=
  F1B.kanLeftKanExtension_refl_of_canonicalColimits (indYoneda κ C) G
    (indContinuous_canonicalColimits κ G · hG)

end SerrePositivity.InfinityCategories.F2.Ind
