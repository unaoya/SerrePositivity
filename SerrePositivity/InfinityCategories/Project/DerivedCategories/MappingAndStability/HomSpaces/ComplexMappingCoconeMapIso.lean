module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.ComplexMappingCoconeMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleFunctorResolutionHomExt
/-!
概要：実可換正方形の両辺が同型なら、同じ mapping cocone の写像も同型にする。
方針：実二成分の回収式で逆との二合成を検証する。
規約：比較 cochain と実射影を保持。使われ方：comma の Hom 射影の準同型性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded CochainComplex HomComplex
variable {R : Type u} [CommRing R] {K₁ L₁ K₂ L₂ : Complex R}
  (d₁ : K₁ ⟶ L₁) (d₂ : K₂ ⟶ L₂) (a : K₁ ≅ K₂) (b : L₁ ≅ L₂)
  (h : d₁ ≫ b.hom = a.hom ≫ d₂) (h' : d₂ ≫ b.inv = a.inv ≫ d₁)
/-- 同じ可換正方形と逆正方形の cocone 写像の合成は恒等。 -/
lemma complexMappingCoconeMap_inverse_comp :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap d₁ d₂ a.hom b.hom h ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap d₂ d₁ a.inv b.inv h' = 𝟙 _ := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgMappingCocone_hom_ext d₁
  · calc
      _ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap d₁ d₂ a.hom b.hom h ≫
          (mappingCocone.fst d₂ ≫ a.inv) := by
        rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst]
      _ = (mappingCocone.fst d₁ ≫ a.hom) ≫ a.inv := by
        rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst]
      _ = _ := by simp
  · apply Cochain.ext
    intro p q hpq
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, HomologicalComplex.comp_f,
      HomologicalComplex.id_f, Category.id_comp]
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_f_snd_v,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_f_snd_v, Category.assoc,
      ← HomologicalComplex.comp_f, b.hom_inv_id, HomologicalComplex.id_f, Category.comp_id]
/-- 元の同型正方形から得る、実二成分を保持する cocone の同型。 -/
def complexMappingCoconeMapIso : mappingCocone d₁ ≅ mappingCocone d₂ := by
  have h' : d₂ ≫ b.inv = a.inv ≫ d₁ := by
    apply (cancel_mono b.hom).1
    rw [Category.assoc, b.inv_hom_id, Category.comp_id, Category.assoc, h,
      ← Category.assoc, a.inv_hom_id, Category.id_comp]
  exact
    { hom := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap d₁ d₂ a.hom b.hom h
      inv := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap d₂ d₁ a.inv b.inv h'
      hom_inv_id := complexMappingCoconeMap_inverse_comp d₁ d₂ a b h h'
      inv_hom_id := complexMappingCoconeMap_inverse_comp d₂ d₁ a.symm b.symm h' h }
end SerrePositivity.InfinityCategories.Project.DerivedCategories
