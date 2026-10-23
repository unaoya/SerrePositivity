module

public import SerrePositivity.InfinityCategories.F1.Coherent.ResolutionEnriched

/-!
概要：旗の解像への標準比較とパラメーター付きの作用の整合性。
方針：二つの入力を同じ最大元の射影で引き戻し、元の写像の自然性を使う。
規約：対象ごとの比較だけでなく任意のパラメーター単体集合を保持する。
使われ方：Kerodon Proposition 4.6.7.16、Corollary 5.6.0.6、解像への coherent な比較の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：解像への標準比較はパラメーター付き写像の作用と可換。
方針：比較射の各単体の公式を使い、二入力を同じ射影で引き戻してから写像を評価する。
規約：X、Y、T の Kan 性は不要。
使われ方：Kerodon Proposition 4.6.7.16、標準比較の豊穣自然性。 -/
lemma coherentResolutionParameterizedMap_comparison {X Y T : SSet.{u}} (f : X ⊗ T ⟶ Y) :
    (coherentResolutionComparison X ▷ T) ≫ coherentResolutionParameterizedMap f =
      f ≫ coherentResolutionComparison Y := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨x, t⟩
  change (coherentResolutionParameterizedMap f).app _
    ((coherentResolutionComparison X).app _ x, t) =
      (coherentResolutionComparison Y).app _ (f.app _ (x, t))
  rw [coherentResolutionComparison_app, coherentResolutionComparison_app]
  apply ULift.ext
  change lift (coherentResolutionProjection n ≫ SSet.yonedaEquiv.symm x)
      (coherentResolutionProjection n ≫ SSet.yonedaEquiv.symm t) ≫ f =
    coherentResolutionProjection n ≫ SSet.yonedaEquiv.symm (f.app _ (x, t))
  rw [← comp_lift]
  rw [Category.assoc]
  congr 1
  exact SSet.yonedaEquiv_symm_comp (x, t) f

/-- 概要：標準比較は内部 Hom の豊穣評価と可換。
方針：任意パラメーターの比較公式を内部 Hom の評価へ適用する。
規約：二つの内部 Hom の射は uncurry した形で比較する。
使われ方：Kerodon Corollary 5.6.0.6、解像の豊穣自己関手への自然な比較の条件。 -/
lemma coherentResolutionEnrichedMap_comparison (X Y : SSet.{u}) :
    (coherentResolutionComparison X ▷ (ihom X).obj Y) ≫
        uncurry (coherentResolutionEnrichedMap X Y) =
      uncurry (𝟙 ((ihom X).obj Y)) ≫ coherentResolutionComparison Y := by
  rw [coherentResolutionEnrichedMap, uncurry_curry]
  exact coherentResolutionParameterizedMap_comparison _

/-- 概要：解像の豊穣作用は標準比較の後で元の内部 Hom の単体を評価した結果に一致する。
方針：豊穣自然性を制限したパラメーター単体で評価し、豊穣作用の単体的自然性を使う。
規約：α は n から k への単体圏の反対圏の射。
使われ方：Kerodon Corollary 5.6.0.6、標準比較を coherent な変換の単体として組み立てる。 -/
lemma coherentResolutionEnrichedMap_app_comparison (X Y : SSet.{u})
    {n k : SimplexCategoryᵒᵖ} (η : ((ihom X).obj Y).obj n) (α : n ⟶ k) (x : X.obj k) :
    (((coherentResolutionEnrichedMap X Y).app n η).app k α)
        ((coherentResolutionComparison X).app k x) =
      (coherentResolutionComparison Y).app k (η.app k α x) := by
  have h := congrArg (fun f : X ⊗ (ihom X).obj Y ⟶ coherentResolutionRightAdjoint.obj Y ↦
      f.app k (x, ((ihom X).obj Y).map α η))
    (coherentResolutionEnrichedMap_comparison X Y)
  have hn := ConcreteCategory.congr_hom
    ((coherentResolutionEnrichedMap X Y).naturality α) η
  change ((ihom (coherentResolutionRightAdjoint.obj X)).obj
      (coherentResolutionRightAdjoint.obj Y)).map α
        ((coherentResolutionEnrichedMap X Y).app n η) =
      (coherentResolutionEnrichedMap X Y).app k (((ihom X).obj Y).map α η) at hn
  change (((coherentResolutionEnrichedMap X Y).app k (((ihom X).obj Y).map α η)).app k (𝟙 k))
      ((coherentResolutionComparison X).app k x) =
    (coherentResolutionComparison Y).app k ((((ihom X).obj Y).map α η).app k (𝟙 k) x) at h
  rw [← hn] at h
  change (((coherentResolutionEnrichedMap X Y).app n η).app k (α ≫ 𝟙 k))
      ((coherentResolutionComparison X).app k x) =
    (coherentResolutionComparison Y).app k (η.app k (α ≫ 𝟙 k) x) at h
  simpa only [Category.comp_id] using h

end SerrePositivity.InfinityCategories
