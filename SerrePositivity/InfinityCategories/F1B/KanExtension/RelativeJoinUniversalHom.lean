module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinRightHom
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinFunctorMappingSpace
public import SerrePositivity.InfinityCategories.F1B.KanExtension.UniversalProperty

/-!
概要：fiber ごとに普遍な相対 join 図式の両端を結ぶ Hom 全単射。
方針：右端への Hom 対応を逆にたどり、左端への制限の全単射と合成する。
規約：元の Kan 変換との公式の同定は別に行う。
使われ方：点ごとの Kan 条件から大域的な普遍写像性への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：普遍な相対 join 図式の右端から出る射は左端での指定底射に沿う射と同値。
方針：右端の Hom 対応の逆と左端への制限の全単射を合成し、底射影を同定する。
規約：全 fiber の余極限性は H のみに課す。
使われ方：Kan の大域的 Hom 普遍性の候補となる全単射。 -/
def kanRelativeJoinUniversalHomEquiv {K C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    (p : K ⟶ C) [CocartesianFibration p] (H : relativeJoin p (𝟙 C) ⟶ D)
    (hcol : ∀ c : C _⦋0⦌, IsColimitCone (kanRelativeJoinFiberCocone p c H)) (G : C ⟶ D) :
    FunctorHom (relativeJoinInr p (𝟙 C) ≫ H) G ≃
      FunctorHom (relativeJoinInl p (𝟙 C) ≫ H) (p ≫ G) :=
  (kanRelativeJoinRightHomEquiv p H G).symm.trans
    ((Equiv.ofBijective _ (kanRelativeJoinFunctor_homMap_bijective p H
      (relativeJoinBaseProjection p (𝟙 C) ≫ G) hcol)).trans
        (kanFunctorHomCongr (U := relativeJoinInl p (𝟙 C) ≫ H)
          (V := relativeJoinInl p (𝟙 C) ≫ (relativeJoinBaseProjection p (𝟙 C) ≫ G)) rfl (by
            rw [← Category.assoc, kanRelativeJoinInl_baseProjection])))

/-- 概要：相対 join の大域的な単位を左端へ制限した Kan 変換。
方針：単位の類を左包含で前合成し、底射影と p の厳密な一致で終点を移す。
規約：元の図式から右端の図式の p による制限への射。
使われ方：両端の Hom 全単射を指定変換の式で表示する。 -/
def kanRelativeJoinUnitLeft {K C D : SSet.{u}} [Quasicategory D]
    (p : K ⟶ C) (H : relativeJoin p (𝟙 C) ⟶ D) :
    FunctorHom (relativeJoinInl p (𝟙 C) ≫ H) (p ≫ (relativeJoinInr p (𝟙 C) ≫ H)) :=
  (hoFunctor.map ((pre (relativeJoinInl p (𝟙 C))).app D)).toFunctor.map
    (kanRelativeJoinUnitHom p H) ≫
      eqToHom (congrArg (fun q ↦ HomotopyCategory.mk (functorVertex q))
        (show relativeJoinInl p (𝟙 C) ≫
            (relativeJoinBaseProjection p (𝟙 C) ≫ (relativeJoinInr p (𝟙 C) ≫ H)) =
              p ≫ (relativeJoinInr p (𝟙 C) ≫ H) by
          rw [← Category.assoc, kanRelativeJoinInl_baseProjection]))

/-- 概要：両端の Hom 全単射は左端の単位による Kan の標準比較写像。
方針：右端の逆対応の単位公式を制限し、底射影と左包含の合成を p と同定する。
規約：ここでの指定変換は kanRelativeJoinUnitLeft。
使われ方：局所余極限性から大域的 Hom 普遍性への第一の接続。 -/
lemma kanRelativeJoinUniversalHomEquiv_apply {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [CocartesianFibration p]
    (H : relativeJoin p (𝟙 C) ⟶ D)
    (hcol : ∀ c : C _⦋0⦌, IsColimitCone (kanRelativeJoinFiberCocone p c H)) (G : C ⟶ D)
    (τ : FunctorHom (relativeJoinInr p (𝟙 C) ≫ H) G) :
    kanRelativeJoinUniversalHomEquiv p H hcol G τ =
      leftKanHomMap p (kanRelativeJoinUnitLeft p H) G τ := by
  have hL : relativeJoinInl p (𝟙 C) ≫ (relativeJoinBaseProjection p (𝟙 C) ≫ G) = p ≫ G := by
    rw [← Category.assoc, kanRelativeJoinInl_baseProjection]
  change 𝟙 _ ≫
      (hoFunctor.map ((pre (relativeJoinInl p (𝟙 C))).app D)).toFunctor.map
        ((kanRelativeJoinRightHomEquiv p H G).symm τ) ≫
      eqToHom (congrArg (fun q ↦ HomotopyCategory.mk (functorVertex q)) hL) = _
  rw [Category.id_comp, kanRelativeJoinRightHomEquiv_symm_apply,
    CategoryTheory.Functor.map_comp]
  have hp :
      (hoFunctor.map ((pre (relativeJoinBaseProjection p (𝟙 C))).app D)).toFunctor ⋙
        (hoFunctor.map ((pre (relativeJoinInl p (𝟙 C))).app D)).toFunctor =
          (hoFunctor.map ((pre p).app D)).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp,
      ← NatTrans.comp_app, ← pre_map, kanRelativeJoinInl_baseProjection]
  have hh := CategoryTheory.Functor.congr_hom hp τ
  erw [hh]
  simp only [leftKanHomMap, kanRelativeJoinUnitLeft, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id]

/-- 概要：fiber ごとに普遍な相対 join 図式の左端の単位は大域的 Hom 普遍性を持つ。
方針：両端の Hom 全単射を単位による標準比較写像と同定する。
規約：元の指定 Kan 変換との一致はこの定理の仮定にも結論にも含まない。
使われ方：指定変換との比較を終えた後の Kan の大域的一意性への入力。 -/
lemma kanRelativeJoinUnitLeft_homUniversal {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [CocartesianFibration p]
    (H : relativeJoin p (𝟙 C) ⟶ D)
    (hcol : ∀ c : C _⦋0⦌, IsColimitCone (kanRelativeJoinFiberCocone p c H)) :
    LeftKanHomUniversal p (kanRelativeJoinUnitLeft p H) := by
  intro G
  have h : (kanRelativeJoinUniversalHomEquiv p H hcol G :
      FunctorHom (relativeJoinInr p (𝟙 C) ≫ H) G → _) =
        leftKanHomMap p (kanRelativeJoinUnitLeft p H) G :=
    funext (kanRelativeJoinUniversalHomEquiv_apply p H hcol G)
  rw [← h]
  exact (kanRelativeJoinUniversalHomEquiv p H hcol G).bijective

end SerrePositivity.InfinityCategories.F1B
