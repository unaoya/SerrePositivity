module
public import SerrePositivity.KST.SConstruction.DGGluingHomCoconeModel

/-! # 右軸を標的とする実 Hom の右作用 cocone 表示
概要：元の右軸への Hom の実零左成分を消し、同じ右作用の cocone と同定する。
方針：閉零左対象への全 Hom の零性と、元の右作用の定義を使う。
規約：元の右 Hom 射影と比較 cochain を保持。使われ方：二軸列の標準モデル比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (z : C) (hz : IsZero (ForgetEnrichment.of (Complex R) z))
  (T X : DGGluingObject R C D M)

/-- 元の右軸への比較差は、同じ右作用と元の右射影を経由する。 -/
lemma dgGluingRightAxisDifference_square :
    dgGluingDifference R C D M T (dgGluingRightAxisObject R C D M z X.right) ≫
      (Iso.refl (M.value T.left X.right)).hom =
    (biprodZeroLeftIso (L := homObject R D T.right X.right)
      (dgHom_isZero_of_closed_zero_target R z hz T.left)).hom ≫
        dgGluingRightAction R C D M T X := by
  change dgGluingDifference R C D M T (dgGluingRightAxisObject R C D M z X.right) ≫
    𝟙 _ = biprod.snd ≫ dgGluingRightAction R C D M T X
  rw [Category.comp_id]
  apply biprod.hom_ext'
  · exact (dgHom_isZero_of_closed_zero_target R z hz T.left).eq_of_src _ _
  · simp only [dgGluingDifference, Preadditive.comp_sub, biprod.inr_snd_assoc,
      biprod.inr_fst_assoc, zero_comp, sub_zero]
    erw [biprod.inr_snd_assoc]
    rfl

/-- 元の右軸 Hom から、同じ入力右作用の cocone への実鎖同型。 -/
def dgGluingRightAxisHomCoconeIso :
    homObject R (DGGluingObject R C D M) T (dgGluingRightAxisObject R C D M z X.right) ≅
      mappingCocone (dgGluingRightAction R C D M T X) :=
  complexMappingCoconeMapIso
    (dgGluingDifference R C D M T (dgGluingRightAxisObject R C D M z X.right)) _
    (biprodZeroLeftIso (dgHom_isZero_of_closed_zero_target R z hz T.left)) (Iso.refl _)
    (dgGluingRightAxisDifference_square R C D M z hz T X)

/-- 同じ同型は、元の右 Hom 射影を厳密に回収する。 -/
lemma dgGluingRightAxisHomCoconeIso_fst :
    (dgGluingRightAxisHomCoconeIso R C D M z hz T X).hom ≫
      mappingCocone.fst (dgGluingRightAction R C D M T X) =
      dgGluingRightHomMap R C D M T (dgGluingRightAxisObject R C D M z X.right) :=
  complexMappingCoconeMap_fst _ _ _ _ (dgGluingRightAxisDifference_square R C D M z hz T X)

/-- 同じ同型は、元の全比較 cochain を恒等係数で保持する。 -/
lemma dgGluingRightAxisHomCoconeIso_snd :
    (Cochain.ofHom (dgGluingRightAxisHomCoconeIso R C D M z hz T X).hom).comp
      (mappingCocone.snd (dgGluingRightAction R C D M T X)) (zero_add (-1)) =
      dgGluingHomPrimitive R C D M T (dgGluingRightAxisObject R C D M z X.right) := by
  exact (complexMappingCoconeMap_snd _ _ _ _
    (dgGluingRightAxisDifference_square R C D M z hz T X)).trans (Cochain.comp_id _)

end SerrePositivity.KST.SConstruction
