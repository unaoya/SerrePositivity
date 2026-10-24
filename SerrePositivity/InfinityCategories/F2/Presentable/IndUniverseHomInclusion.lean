module

public import SerrePositivity.InfinityCategories.F2.Ind.IndContinuousLeftKan
public import SerrePositivity.InfinityCategories.F2.Presentable.PresheafUniverseArbitraryColimits
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseYonedaComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseCoconeRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseLeftKanCanonical
public import SerrePositivity.InfinityCategories.F2.Compact.UniverseCoconePostcomposition

/-!
概要：Ind の元の包含を大きい Hom 係数前層と比較するための宇宙変更。
方針：公開された Ind 密度比較を前層宇宙変更と合成する。
規約：Ind 側を編集せず、元の全 Yoneda と密度余錐を保持する。
使われ方：filtered 延長と simplicial Ind 表示の全 Hom 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind

/-- 概要：Ind の包含と指定前層宇宙変更の合成。
方針：元の包含全体を持ち上げる。
規約：対象と全射を保持する。
使われ方：全 Hom 係数族の始域。 -/
def indUniverseHomInclusion (κ : Cardinal.{u}) (C : SSet.{u}) [Quasicategory C] :
    (SSet.uliftFunctor.{u + 2, u + 1}).obj (IndInfinity κ C) ⟶
      PresheafInfinity ((SSet.uliftFunctor.{u + 1, u}).obj C) :=
  (SSet.uliftFunctor.{u + 2, u + 1}).map (indInclusionPresheaf κ C) ≫ presheafUniverseDiagram C

/-- 概要：元の Ind Yoneda の像は大きい Yoneda と全自然同型。
方針：元の厳密な因子化と既存の Yoneda 宇宙比較を使う。
規約：同じ全関手の比較である。
使われ方：両 Hom 族の Yoneda 制限の同定。 -/
def indUniverseHomYonedaIso (κ : Cardinal.{u}) (C : SSet.{u}) [Quasicategory C] :
    FunctorIso ((SSet.uliftFunctor.{u + 2, u + 1}).map (indYoneda κ C) ≫
      indUniverseHomInclusion κ C) (yonedaInfinityMap ((SSet.uliftFunctor.{u + 1, u}).obj C)) := by
  dsimp only [indUniverseHomInclusion]
  rw [← Category.assoc, ← Functor.map_comp, indYoneda_inclusion]
  exact yonedaInfinityMap_universeIso C

/-- 概要：Ind の元の標準 Kan 全余錐の包含像を宇宙変更しても余極限となる。
方針：同じ小さい密度比較に制限し、前層宇宙変更の保存性を使う。
規約：κ-filtered 交換定理を入力にしない。
使われ方：大きい包含の標準 Kan 条件。 -/
lemma indUniverseHomCanonical_image_isColimit (κ : Cardinal.{u}) {C : SSet.{u}}
    [Quasicategory C] (v : (IndInfinity κ C) _⦋0⦌) :
    IsColimitCone (mapJoinCocone (presheafUniverseDiagram C)
      (JoinCocone.ulift.{u + 1, u + 2}
        (leftKanCanonicalCocone (indYoneda κ C) (indInclusionPresheaf κ C) v))) := by
  let c := leftKanCanonicalCocone (indYoneda κ C) (indInclusionPresheaf κ C) v
  let e := indElementsLeftKanComparison κ v
  apply (isColimitCone_iff_restrict_equivalentShape
    ((SSet.uliftFunctor.{u + 2, u + 1}).map e)
    (IsQCatEquivalence.ulift.{u + 1, u + 2}
      (indElementsLeftKanComparison_isQCatEquivalence κ v)) _).mpr
  have hi : IsColimitCone (mapJoinCocone (indInclusionPresheaf κ C)
      (indVertexDensityCocone κ v)) :=
    (F2.isColimitCone_iff_of_cocone_val_eq _ _
      (indVertexDensityCocone_val_inclusion κ v)).mpr
        (presheafDensityCocone_isColimit (indVertexPresheaf κ v))
  have hd := presheafUniverseDiagram_map_isColimit _ _ hi
  apply (F2.isColimitCone_iff_of_cocone_val_eq _ _ ?_).mpr hd
  change joinMap ((SSet.uliftFunctor.{u + 2, u + 1}).map e) (𝟙 _) ≫
    ((JoinCocone.ulift.{u + 1, u + 2} c).val ≫ presheafUniverseDiagram C) = _
  rw [← Category.assoc, ← ulift_restrictJoinCocone_val]
  change ((uliftCoconeShapeIso _ 0).inv ≫
    (SSet.uliftFunctor.{u + 2, u + 1}).map (c.restrict e).val) ≫ presheafUniverseDiagram C = _
  rw [show (c.restrict e).val =
      (mapJoinCocone (indInclusionPresheaf κ C) (indVertexDensityCocone κ v)).val from
    indLeftKanCanonicalCocone_restrict_val κ (indInclusionPresheaf κ C) v]
  rfl

/-- 概要：大きい Ind 包含の全標準左 Kan 余錐は余極限。
方針：同じ宇宙比較で指定全余錐の普遍性を戻す。
規約：元の Yoneda の持ち上げを保持する。
使われ方：自然変換空間族の右 Kan 条件。 -/
lemma indUniverseHomInclusion_canonicalColimits (κ : Cardinal.{u}) {C : SSet.{u}}
    [Quasicategory C] :
    ∀ v : ((SSet.uliftFunctor.{u + 2, u + 1}).obj (IndInfinity κ C)) _⦋0⦌,
      IsColimitCone (leftKanCanonicalCocone
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (indYoneda κ C))
        (indUniverseHomInclusion κ C) v) := by
  rintro ⟨v⟩
  exact leftKanCanonicalCocone_post_ulift_isColimit (indYoneda κ C)
    (indInclusionPresheaf κ C) v (presheafUniverseDiagram C)
    (indUniverseHomCanonical_image_isColimit κ v)

end SerrePositivity.InfinityCategories.F2.Presentable
