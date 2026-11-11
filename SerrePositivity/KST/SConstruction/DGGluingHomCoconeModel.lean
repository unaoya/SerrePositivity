module
public import SerrePositivity.KST.SConstruction.MappingCoconeZeroLeft
public import SerrePositivity.KST.SConstruction.DGGluingAxesMixedHom

/-! # 元の gluing Hom の二成分 cocone 表示
概要：元の比較差とその右軸制限を、同じ左右作用による標準 cocone に同定する。
方針：実比較差の二成分を照合し、左右の射影と比較 cochain を保持する同型を使う。
規約：全整数次数の実鎖同型。使われ方：元の二軸列の評価短完全性。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (T X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

/-- 元の比較差は、負の左作用と同じ右作用からの標準直和射。 -/
lemma dgGluingDifference_eq_desc :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M T X =
      biprod.desc (-_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M T X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M T X) := by
  apply biprod.hom_ext'
  · simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference, Preadditive.comp_sub, biprod.inl_snd_assoc,
      biprod.inl_fst_assoc, zero_comp, zero_sub, biprod.inl_desc]
  · simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference, Preadditive.comp_sub, biprod.inr_snd_assoc,
      biprod.inr_fst_assoc, zero_comp, sub_zero, biprod.inr_desc]

/-- 同じ比較差から二成分標準 cocone への実同型。 -/
def dgGluingHomBiprodCoconeIso :
    homObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) T X ≅
      mappingCocone (biprod.desc (-_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M T X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M T X)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMapIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M T X) _
    (Iso.refl _) (Iso.refl _) (by
      simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp] using
        dgGluingDifference_eq_desc R C D M T X)

/-- 同じ標準化は、元の左右射影をまとめた第一射影を保持する。 -/
lemma dgGluingHomBiprodCoconeIso_fst :
    (dgGluingHomBiprodCoconeIso R C D M T X).hom ≫
      mappingCocone.fst (biprod.desc (-_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M T X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M T X)) =
      mappingCocone.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M T X) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst _ _ _ _ (by
    simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp] using
      dgGluingDifference_eq_desc R C D M T X)).trans (Category.comp_id _)

/-- 同じ標準化は、元の全比較 cochain を保持する。 -/
lemma dgGluingHomBiprodCoconeIso_snd :
    (Cochain.ofHom (dgGluingHomBiprodCoconeIso R C D M T X).hom).comp
      (mappingCocone.snd (biprod.desc (-_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M T X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M T X))) (zero_add (-1)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M T X := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_snd _ _ _ _ (by
    simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp] using
      dgGluingDifference_eq_desc R C D M T X)).trans (Cochain.comp_id _)

end SerrePositivity.KST.SConstruction
