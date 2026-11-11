module
public import SerrePositivity.KST.SConstruction.DGGluingRightAxisCoconeModel
public import SerrePositivity.KST.SConstruction.DGGluingAxisRightPrimitive
public import SerrePositivity.KST.SConstruction.DGGluingAxisRightPostComponents
public import SerrePositivity.KST.SConstruction.MappingCoconeBiprodCofiber

/-! # 元の右軸射と標準二成分 cocone 包含の一致
概要：元の右軸包含の全 Hom 後合成を、標準第二 cocone 包含に厳密に照合する。
方針：元の二射影と第三 cochain の三成分をすべて保持して比較する。
規約：実鎖同型の可換正方形。使われ方：元の二軸列の評価短完全性。
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
  (T X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "Y" => dgGluingRightAxisObject R C D M z X.right
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M T Y X
  (dgGluingAxisRightInclusion R C D M z hz X)
local notation "a" => -_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M T X
local notation "b" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M T X

/-- 同じ右軸射の全 Hom 第一成分は、元の右射影と標準右包含の合成。 -/
lemma dgGluingAxisRightInclusion_post_fst :
    p ≫ mappingCocone.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M T X) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M T Y ≫ biprod.inr := by
  apply biprod.hom_ext
  · change p ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M T X =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M T Y ≫ biprod.inr) ≫ biprod.fst
    rw [dgGluingAxisRightInclusion_post_left, Category.assoc, biprod.inr_fst, comp_zero]
  · change p ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M T X =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M T Y ≫ biprod.inr) ≫ biprod.snd
    rw [dgGluingAxisRightInclusion_post_right, Category.assoc, biprod.inr_snd,
      Category.comp_id]

/-- 元の右軸射と同じ標準 cocone 包含は、第三 cochain も保って厳密に可換。 -/
lemma dgGluingAxesCoconeInclusion_square :
    p ≫ (dgGluingHomBiprodCoconeIso R C D M T X).hom =
      (dgGluingRightAxisHomCoconeIso R C D M z hz T X).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodInclusion a b := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgMappingCocone_hom_ext (biprod.desc a b)
  · have hl : (p ≫ (dgGluingHomBiprodCoconeIso R C D M T X).hom) ≫
        mappingCocone.fst (biprod.desc a b) =
        p ≫ mappingCocone.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M T X) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun k => p ≫ k) (dgGluingHomBiprodCoconeIso_fst R C D M T X))
    have hr : ((dgGluingRightAxisHomCoconeIso R C D M z hz T X).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodInclusion a b) ≫ mappingCocone.fst (biprod.desc a b) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M T Y ≫ biprod.inr := by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodInclusion,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst, ← Category.assoc,
        dgGluingRightAxisHomCoconeIso_fst]
      rfl
    exact hl.trans ((dgGluingAxisRightInclusion_post_fst R C D M z hz T X).trans hr.symm)
  · rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
      dgGluingHomBiprodCoconeIso_snd, dgGluingAxisRightInclusion_post_primitive,
      Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
    have hi : (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodInclusion a b)).comp
        (mappingCocone.snd (biprod.desc a b)) (zero_add (-1)) = mappingCocone.snd b :=
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_snd b (biprod.desc a b) biprod.inr (𝟙 _) (by simp)).trans
        (Cochain.comp_id _)
    rw [hi]
    exact (dgGluingRightAxisHomCoconeIso_snd R C D M z hz T X).symm

end SerrePositivity.KST.SConstruction
