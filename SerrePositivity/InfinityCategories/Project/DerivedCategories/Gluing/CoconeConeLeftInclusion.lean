module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ConeCoconeLeftInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.YonedaConeEvaluation

/-! 回収した Hom 円錐の交換同型は、同じ次数 −1 の左包含の両成分を保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R] {P Q S T : Complex R}
  (μ : P ⟶ Q) (ν : S ⟶ T) (f : P ⟶ S)
  (k : mappingCocone μ ⟶ mappingCocone ν)
  (hf : k ≫ mappingCocone.fst ν = mappingCocone.fst μ ≫ f)
local notation "g" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractBottom μ ν f k hf
local notation "h" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractHomotopy μ ν k
local notation "hh" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractHomotopy_boundary μ ν f k hf
local notation "ℓ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractConeArrow μ ν f k hf

/-- 回収した交換同型の左包含の第一成分は、同じ第一射影と cone 左包含。 -/
lemma dgGluingCoconeExtractConeIso_inl_fst :
    (mappingCone.inl k).comp
      (Cochain.ofHom ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractConeIso μ ν f k hf).hom ≫ mappingCocone.fst ℓ))
      (add_zero (-1)) =
    (Cochain.ofHom (mappingCocone.fst μ)).comp (mappingCone.inl f) (zero_add (-1)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractConeIso, Iso.trans_hom, Category.assoc, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_third_is_zero_cochain]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeInl_eqToIso k _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractMap_recovery μ ν f k hf).symm]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeCoconeMap_inl_fst f g μ ν h hh

/-- 回収した交換同型の左包含の第三 cochain も、元の同じ第三成分の負。 -/
lemma dgGluingCoconeExtractConeIso_inl_snd :
    (mappingCone.inl k).comp
      ((Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractConeIso μ ν f k hf).hom).comp
        (mappingCocone.snd ℓ) (zero_add (-1))) (by omega : -1 + -1 = -2) =
    -(mappingCocone.snd μ).comp (mappingCone.inl g) (by omega : -1 + -1 = -2) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractConeIso, Iso.trans_hom, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_second_is_zero_cochain]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeInl_eqToIso k _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractMap_recovery μ ν f k hf).symm]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeCoconeMap_inl_snd f g μ ν h hh

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
