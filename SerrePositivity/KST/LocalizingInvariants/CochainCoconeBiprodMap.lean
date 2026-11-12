module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexMappingCoconeBiprod
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionHomExt

/-!
概要：二成分の cocone の元の包含は、元の三成分の可換正方形に自然である。
方針：同じ cocone の実射影と比較 cochain を計算し、二成分の一意性を使う。
規約：短完全列の元の包含を保持。使われ方：平方零拡大の層の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] {K L T K' L' T' : Complex R}
  (a : K ⟶ T) (b : L ⟶ T) (a' : K' ⟶ T') (b' : L' ⟶ T')
  (x : K ⟶ K') (y : L ⟶ L') (z : T ⟶ T')
  (ha : a ≫ z = x ≫ a') (hb : b ≫ z = y ≫ b')

include ha hb in
lemma cochainCoconeBiprodMap_comm : biprod.desc a b ≫ z =
    biprod.map x y ≫ biprod.desc a' b' := by
  apply biprod.hom_ext'
  · simp only [← Category.assoc, biprod.inl_desc, biprod.inl_map]
    rw [Category.assoc, biprod.inl_desc]
    exact ha
  · simp only [← Category.assoc, biprod.inr_desc, biprod.inr_map]
    rw [Category.assoc, biprod.inr_desc]
    exact hb

lemma cochainCoconeBiprodInclusion_naturality : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodInclusion a b ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap (biprod.desc a b) (biprod.desc a' b') (biprod.map x y) z
      (cochainCoconeBiprodMap_comm a b a' b' x y z ha hb) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap b b' y z hb ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodInclusion a' b' := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgMappingCocone_hom_ext (biprod.desc a' b')
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodInclusion, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst,
      Category.assoc, biprod.inr_map]
    rw [← Category.assoc, Category.assoc _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodInclusion a' b'),
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodInclusion, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst, Category.assoc]
  · rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_snd, ← Cochain.comp_assoc_of_first_is_zero_cochain]
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodInclusion, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_snd]
    rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodInclusion, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_snd]
    simpa using (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_snd b b' y z hb).symm

end SerrePositivity.KST.LocalizingInvariants
