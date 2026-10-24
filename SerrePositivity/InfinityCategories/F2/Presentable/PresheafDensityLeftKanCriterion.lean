module

public import SerrePositivity.InfinityCategories.F2.Presentable.PresheafNativeDensityKan

/-!
概要：前層の密度余錐の像から元の関手の Yoneda 左 Kan 条件を判定する。
方針：標準局所余錐を小さい elements 比較で制限して同じ像へ戻す。
規約：標的の全小余極限や関手の全小余極限保存は要求しない。
使われ方：前層の普遍性と反対密度による表現可能性の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind
variable {A : SSet.{u}} [Quasicategory A] {E : SSet.{u + 1}} [Quasicategory E]
  (F : PresheafInfinity A ⟶ E)

omit [Quasicategory E] in
/-- 概要：標準 Yoneda 局所余錐の制限は元の密度余錐の同じ像。
方針：小さい elements 比較の普遍余錐の等式を後合成する。
規約：指定された関手 F と全余錐の値を保持する。
使われ方：密度保存からの局所 Kan 条件。 -/
lemma presheafLeftKanCanonicalCocone_restrict_val
    (P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u}) :
    ((leftKanCanonicalCocone (yonedaInfinityMap A) F (functorVertex P)).restrict
      (presheafElementsLeftKanComparison P)).val =
        (mapJoinCocone F (presheafDensityCocone P)).val := by
  exact (Category.assoc _ _ F).symm.trans
    (congrArg (fun g ↦ g ≫ F) (presheafElementsLeftKanComparison_coconeMap P))

/-- 概要：全密度余錐の像が余極限なら元の標準局所余錐も余極限。
方針：小さい elements 比較の同値で標準余錐を制限する。
規約：元の全前層圏を始域に保つ。
使われ方：全関手の Yoneda 左 Kan 普遍性。 -/
lemma presheaf_densityImages_canonicalColimits
    (hF : ∀ P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u},
      IsColimitCone (mapJoinCocone F (presheafDensityCocone P)))
    (v : (PresheafInfinity A) _⦋0⦌) :
    IsColimitCone (leftKanCanonicalCocone (yonedaInfinityMap A) F v) := by
  obtain ⟨P, rfl⟩ := (presheafInfinityObjectEquiv A).surjective v
  apply (isColimitCone_iff_restrict_equivalentShape
    (presheafElementsLeftKanComparison P) (presheafElementsLeftKanComparison_isQCatEquivalence P)
    _).mpr
  exact (F2.isColimitCone_iff_of_cocone_val_eq _ _
    (presheafLeftKanCanonicalCocone_restrict_val F P)).mpr (hF P)

/-- 概要：密度余錐を保つ元の関手は同じ Yoneda 制限の恒等単位付き左 Kan 延長。
方針：証明した全標準局所余極限を元の Kan 判定へ渡す。
規約：単位の代表を恒等から変更しない。
使われ方：密度による制限の Hom 普遍性。 -/
lemma presheaf_densityImages_isLeftKanExtension
    (hF : ∀ P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u},
      IsColimitCone (mapJoinCocone F (presheafDensityCocone P))) :
    IsLeftKanExtension (yonedaInfinityMap A) (yonedaInfinityMap A ≫ F) F
      (functorHomotopyRefl (yonedaInfinityMap A ≫ F)) :=
  F1B.kanLeftKanExtension_refl_of_canonicalColimits _ _
    (presheaf_densityImages_canonicalColimits F hF)

/-- 概要：密度余錐を保つ二関手の Yoneda 制限の同型を全自然同型へ延長する。
方針：局所 Kan の Hom 全単射で順射と逆射を持ち上げ、同じ制限で両逆を検出する。
規約：元の関手間の全関手同型を構成し、各点の同値だけには弱めない。
使われ方：自由余完備化を使う表現可能性と随伴存在の比較。 -/
def presheafDensityIsoOfYoneda {G : PresheafInfinity A ⟶ E}
    (hF : ∀ P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u},
      IsColimitCone (mapJoinCocone F (presheafDensityCocone P)))
    (hG : ∀ P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u},
      IsColimitCone (mapJoinCocone G (presheafDensityCocone P)))
    (e : FunctorIso (yonedaInfinityMap A ≫ F) (yonedaInfinityMap A ≫ G)) :
    FunctorIso F G := by
  let T := (hoFunctor.map ((pre (yonedaInfinityMap A)).app E)).toFunctor
  have hf := F1B.kanLeftCanonicalHomMap_bijective (yonedaInfinityMap A) F
    (presheaf_densityImages_canonicalColimits F hF)
  have hg := F1B.kanLeftCanonicalHomMap_bijective (yonedaInfinityMap A) G
    (presheaf_densityImages_canonicalColimits G hG)
  let f := ((hf G).surjective e.hom).choose
  have hfe := ((hf G).surjective e.hom).choose_spec
  let g := ((hg F).surjective e.inv).choose
  have hge := ((hg F).surjective e.inv).choose_spec
  refine ⟨f, g, ?_, ?_⟩
  · apply (hf F).injective
    change T.map (f ≫ g) = T.map (𝟙 _)
    rw [CategoryTheory.Functor.map_comp, hfe, hge, e.hom_inv_id, CategoryTheory.Functor.map_id]
    rfl
  · apply (hg G).injective
    change T.map (g ≫ f) = T.map (𝟙 _)
    rw [CategoryTheory.Functor.map_comp, hge, hfe, e.inv_hom_id, CategoryTheory.Functor.map_id]
    rfl

end SerrePositivity.InfinityCategories.F2.Presentable
