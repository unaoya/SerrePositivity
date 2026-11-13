module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.ComplexMappingCoconeMapIso

/-! # 実零左成分を消す mapping cocone 同型
概要：左成分が実零対象のとき、元の比較差を右成分へ制限した cocone と同型にする。
方針：同じ右射影・右包含を逆対とし、比較 cochain を恒等で保つ。
規約：鎖複体の実同型。使われ方：右軸を標的とする全 Hom の同定。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable {R : Type u} [CommRing R] {Z L T : Complex R}

/-- 元の実零左成分を消す、同じ右射影と右包含による同型。 -/
def biprodZeroLeftIso (hZ : IsZero Z) : Z ⊞ L ≅ L where
  hom := biprod.snd
  inv := biprod.inr
  hom_inv_id := by
    apply biprod.hom_ext
    · simpa only [Category.assoc, biprod.inr_fst, comp_zero, Category.id_comp] using
        (hZ.eq_zero_of_tgt (biprod.fst : Z ⊞ L ⟶ Z)).symm
    · simp
  inv_hom_id := biprod.inr_snd

/-- 元の比較差は、実零左成分を消した同じ右制限を経由する。 -/
lemma mappingCoconeZeroLeft_square (hZ : IsZero Z) (d : Z ⊞ L ⟶ T) :
    d ≫ (Iso.refl T).hom = (biprodZeroLeftIso hZ).hom ≫ (biprod.inr ≫ d) := by
  simp only [Iso.refl_hom, Category.comp_id, biprodZeroLeftIso]
  apply biprod.hom_ext'
  · exact hZ.eq_of_src _ _
  · simp

/-- 元の比較差の右制限を使う、比較成分も保持する実 cocone 同型。 -/
def mappingCoconeZeroLeftIso (hZ : IsZero Z) (d : Z ⊞ L ⟶ T) :
    mappingCocone d ≅ mappingCocone (biprod.inr ≫ d) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMapIso d (biprod.inr ≫ d) (biprodZeroLeftIso hZ) (Iso.refl T)
    (mappingCoconeZeroLeft_square hZ d)

/-- 同じ同型の第一射影は、元の右射影を厳密に回収する。 -/
lemma mappingCoconeZeroLeftIso_fst (hZ : IsZero Z) (d : Z ⊞ L ⟶ T) :
    (mappingCoconeZeroLeftIso hZ d).hom ≫ mappingCocone.fst (biprod.inr ≫ d) =
      mappingCocone.fst d ≫ biprod.snd :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst d _ _ _ (mappingCoconeZeroLeft_square hZ d)

/-- 同じ同型は、元の比較 cochain を恒等係数で保持する。 -/
lemma mappingCoconeZeroLeftIso_snd (hZ : IsZero Z) (d : Z ⊞ L ⟶ T) :
    (Cochain.ofHom (mappingCoconeZeroLeftIso hZ d).hom).comp
      (mappingCocone.snd (biprod.inr ≫ d)) (zero_add (-1)) = mappingCocone.snd d := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_snd d _ _ _ (mappingCoconeZeroLeft_square hZ d)).trans
    (Cochain.comp_id _)

end SerrePositivity.KST.SConstruction
