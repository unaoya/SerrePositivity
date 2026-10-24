module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinPrismNaturality
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinUniversalHom

/-!
概要：相対 join の右端の対応の単位と標準 prism の指定変換の同定。
方針：prism の自然性を、底に沿う図式では定値になることと合わせる。
規約：同定するのは h Fun の類であり、代表の raw な一致を要求しない。
使われ方：指定 Kan 変換に対する大域的 Hom 普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：左端への制限は右端の Hom 対応と標準 prism による Kan 比較写像に両立する。
方針：prism の自然性の正方形を底図式の定値な辺で同定する。
規約：H の局所余極限性は不要。
使われ方：単位の左端への制限と指定 prism の類の一致。 -/
lemma kanRelativeJoinTransformation_homMap {K C D : SSet.{u}} [Quasicategory D]
    (p : K ⟶ C) (H : relativeJoin p (𝟙 C) ⟶ D) (G : C ⟶ D)
    (α : FunctorHom H (relativeJoinBaseProjection p (𝟙 C) ≫ G)) :
    (hoFunctor.map ((pre (relativeJoinInl p (𝟙 C))).app D)).toFunctor.map α ≫
        eqToHom (congrArg (fun q ↦ HomotopyCategory.mk (functorVertex q))
          (show relativeJoinInl p (𝟙 C) ≫ (relativeJoinBaseProjection p (𝟙 C) ≫ G) = p ≫ G by
            rw [← Category.assoc, kanRelativeJoinInl_baseProjection])) =
      leftKanHomMap p
        (SSet.Truncated.HomotopyCategory.homMk
          (functorEdgeOfSimplicialHomotopy (kanRelativeJoinTransformation p H))) G
        (kanRelativeJoinRightHomEquiv p H G α) := by
  have hR : p ≫ relativeJoinInr p (𝟙 C) ≫ (relativeJoinBaseProjection p (𝟙 C) ≫ G) =
      p ≫ G := by
    rw [reassoc_of% (relativeJoinInr_baseProjection p (𝟙 C))]
  have h := congrArg
    (fun t ↦ t ≫ eqToHom (congrArg (fun q ↦ HomotopyCategory.mk (functorVertex q)) hR))
    (kanRelativeJoinTransformation_naturality p α)
  rw [kanRelativeJoinTransformation_base_hom] at h
  have hp :
      (hoFunctor.map ((pre (relativeJoinInr p (𝟙 C))).app D)).toFunctor ⋙
        (hoFunctor.map ((pre p).app D)).toFunctor =
          (hoFunctor.map ((pre (p ≫ relativeJoinInr p (𝟙 C))).app D)).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp,
      ← NatTrans.comp_app, ← pre_map]
  have hh := CategoryTheory.Functor.congr_hom hp α
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hh
  simp only [leftKanHomMap, kanRelativeJoinRightHomEquiv_apply,
    CategoryTheory.Functor.map_comp, eqToHom_map]
  erw [hh]
  simpa only [Category.assoc, eqToHom_trans] using h

/-- 概要：右端の Hom 対応の単位を左端へ制限すると標準 prism の指定変換となる。
方針：prism と両端の制限の両立式を単位に適用し、右端の恒等射を消去する。
規約：代表の選択ではなく h Fun の射の等式。
使われ方：元の標準 Kan 変換への大域的 Hom 普遍性の接続。 -/
lemma kanRelativeJoinUnitLeft_eq_transformation {K C D : SSet.{u}} [Quasicategory D]
    (p : K ⟶ C) (H : relativeJoin p (𝟙 C) ⟶ D) :
    kanRelativeJoinUnitLeft p H =
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (kanRelativeJoinTransformation p H)) := by
  have h := kanRelativeJoinTransformation_homMap p H (relativeJoinInr p (𝟙 C) ≫ H)
    (kanRelativeJoinUnitHom p H)
  simp only [leftKanHomMap, kanRelativeJoinUnitHom, Equiv.apply_symm_apply,
    CategoryTheory.Functor.map_id] at h
  change kanRelativeJoinUnitLeft p H =
    SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (kanRelativeJoinTransformation p H)) ≫ 𝟙 _ at h
  simpa only [Category.comp_id] using h

/-- 概要：fiber ごとに普遍な相対 join 図式の標準 prism は大域的 Hom 普遍性を持つ。
方針：単位から得る変換の普遍性を、標準 prism との類の一致で移す。
規約：構造射 p は cocartesian、底と標的は quasicategory。
使われ方：点ごとの Kan 条件から指定変換の大域的な普遍写像性への主経路。 -/
lemma kanRelativeJoinTransformation_homUniversal {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [CocartesianFibration p]
    (H : relativeJoin p (𝟙 C) ⟶ D)
    (hcol : ∀ c : C _⦋0⦌, IsColimitCone (kanRelativeJoinFiberCocone p c H)) :
    LeftKanHomUniversal p (SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (kanRelativeJoinTransformation p H))) := by
  rw [← kanRelativeJoinUnitLeft_eq_transformation]
  exact kanRelativeJoinUnitLeft_homUniversal p H hcol

end SerrePositivity.InfinityCategories.F1B
