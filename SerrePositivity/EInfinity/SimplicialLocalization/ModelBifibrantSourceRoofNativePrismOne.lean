module

public import SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefixPrismOne
public import SerrePositivity.EInfinity.SimplicialLocalization.KanHammockHomPinchedValue
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativePrism
public import SerrePositivity.InfinityCategories.Stable.Roof.SliceEvaluationPinched

/-!
概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory SSet MonoidalCategory SimplicialLocalization
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductCommaNativeSimplex_one {n : ℕ}
    (Γ : Fin (n + 1) ⥤ modelBifibrantSourceRoofProductComma X Y q b) :
    modelBifibrantSourceRoofProductCommaNativeSimplex X Y q b Γ (OrderHom.const _ 1) =
    coherentHomComparisonSimplex
      (C := KanHammockCategory (modelBifibrantRelativeCategory C))
      (X := (kanHammockSourceFunctor (modelBifibrantRelativeCategory C)).obj
        (modelBifibrantObject C (modelBifibrantSourceRoofDegreeObject X Y q b)))
      (Y := (kanHammockSourceFunctor (modelBifibrantRelativeCategory C)).obj
        (modelBifibrantObject C Y))
      ((modelBifibrantSourceRoofProductCommaNativeFamilyMap X Y q b).app (Opposite.op ⦋n⦌) Γ) :=
  RoofPrefix.simplex_one (modelBifibrantRelativeCategory C)
    (modelBifibrantSourceRoofProductCommaDiagram X Y q b)
    (modelBifibrantSourceRoofProductCommaEvaluation X Y q b)
    (modelBifibrantSourceRoofProductCommaEvaluation_weak X Y q b)
    (modelBifibrantSourceRoofProductCommaRightLeg X Y q b)
    (fun f => modelBifibrantSourceRoofProductCommaDiagram_map_weak X Y q b f) Γ

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductCommaNativePinchedMap_app_val {n : ℕ}
    (Γ : (nerve (modelBifibrantSourceRoofProductComma X Y q b)) _⦋n⦌) :
    ((modelBifibrantSourceRoofProductCommaNativePinchedMap X Y q b).app (Opposite.op ⦋n⦌) Γ).val =
    coherentHomComparisonSimplex
      (C := KanHammockCategory (modelBifibrantRelativeCategory C))
      (X := (kanHammockSourceFunctor (modelBifibrantRelativeCategory C)).obj
        (modelBifibrantObject C (modelBifibrantSourceRoofDegreeObject X Y q b)))
      (Y := (kanHammockSourceFunctor (modelBifibrantRelativeCategory C)).obj
        (modelBifibrantObject C Y))
      ((modelBifibrantSourceRoofProductCommaNativeFamilyMap X Y q b).app (Opposite.op ⦋n⦌) Γ) := by
  rw [← modelBifibrantSourceRoofProductCommaNativeFamilyMap_pinched X Y q b]
  exact kanHammockHomPinchedMap_app_val (modelBifibrantRelativeCategory C)
    (modelBifibrantObject C (modelBifibrantSourceRoofDegreeObject X Y q b))
    (modelBifibrantObject C Y)
    ((modelBifibrantSourceRoofProductCommaNativeFamilyMap X Y q b).app (Opposite.op ⦋n⦌) Γ)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductCommaNativePrism_one :
    prismEndpoint 1 (nerve (modelBifibrantSourceRoofProductComma X Y q b)) ≫
      modelBifibrantSourceRoofProductCommaNativePrism X Y q b =
    modelBifibrantSourceRoofProductCommaNativePinchedMap X Y q b ≫
      pinchedFamilySlice (kanHammockNerve (modelBifibrantRelativeCategory C))
        (modelBifibrantHammockVertex (modelBifibrantSourceRoofDegreeObject X Y q b))
        (modelBifibrantHammockVertex Y) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro Γ
  apply Subtype.ext
  change (joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
    (modelBifibrantSourceRoofProductCommaNativeSimplex X Y q b Γ (OrderHom.const _ 1)) =
      (joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
        (((modelBifibrantSourceRoofProductCommaNativePinchedMap X Y q b).app
          (Opposite.op ⦋n⦌) Γ).val)
  rw [modelBifibrantSourceRoofProductCommaNativeSimplex_one X Y q b Γ,
    modelBifibrantSourceRoofProductCommaNativePinchedMap_app_val X Y q b Γ]

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductCommaNativePrism_one_evaluation :
    (β_ (nerve (modelBifibrantSourceRoofProductComma X Y q b)) (Δ[1] : SSet.{max u v})).hom ≫
      rightMappingSpacePrism _ ≫ sliceOverUncurry
        (prismEndpoint 1 _ ≫ modelBifibrantSourceRoofProductCommaNativePrism X Y q b) =
    (intervalFamilyHomotopy (modelBifibrantSourceRoofProductCommaNativePinchedMap X Y q b ≫
      pinchedHomToIntervalMappingSpace _ _)).h := by
  rw [modelBifibrantSourceRoofProductCommaNativePrism_one X Y q b]
  exact (roofSliceEvaluationHomotopy_precomp_h (modelBifibrantHammockVertex Y)
    (modelBifibrantSourceRoofProductCommaNativePinchedMap X Y q b ≫
      pinchedFamilySlice _ _ _)).symm.trans
        (roofSliceEvaluationHomotopy_pinched_h
          (modelBifibrantSourceRoofProductCommaNativePinchedMap X Y q b))

end SerrePositivity.EInfinity.SimplicialLocalization
