module

public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.ComplexMappingCoconeMap

/-!
概要：零の比較 cochain を持つ cocone の斉次持ち上げと、その射への自然性。
方針：cocone の実二射影の回収式と、各次数の恒等分解を使う。
規約：斉次包含を鎖写像とは扱わない。使われ方：相対二端点射の次数全射性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R]

lemma cochainMappingCocone_lift_zero_f {K L M : Complex R} (d : K ⟶ L) (a : M ⟶ K)
    (h : δ (-1) 0 (0 : Cochain M L (-1)) + Cochain.ofHom (a ≫ d) = 0) (n : ℤ) :
    (mappingCocone.lift d a 0 h).f n = a.f n ≫ (mappingCocone.inl d).v n n (add_zero n) := by
  have hd := congrArg (fun t => (mappingCocone.lift d a 0 h).f n ≫ t)
    (mappingCocone.id_X d n (n - 1) (by omega))
  rw [Preadditive.comp_add, ← Category.assoc, mappingCocone.lift_f_fst_f,
    ← Category.assoc, mappingCocone.lift_f_snd_v, Cochain.zero_v, zero_comp,
    add_zero, Category.comp_id] at hd
  exact hd.symm

lemma cochainMappingCoconeMap_inl {K₁ L₁ K₂ L₂ : Complex R}
    (d₁ : K₁ ⟶ L₁) (d₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : d₁ ≫ b = a ≫ d₂) (n : ℤ) :
    (mappingCocone.inl d₁).v n n (add_zero n) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap d₁ d₂ a b comm).f n =
        a.f n ≫ (mappingCocone.inl d₂).v n n (add_zero n) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCocone_X_ext d₂ n
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_f_fst_f, ← Category.assoc,
      mappingCocone.inl_v_fst_f, Category.id_comp, Category.assoc,
      mappingCocone.inl_v_fst_f, Category.comp_id]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_f_snd_v, ← Category.assoc,
      mappingCocone.inl_v_snd_v, zero_comp, Category.assoc,
      mappingCocone.inl_v_snd_v, comp_zero]

end SerrePositivity.KST.LocalizingInvariants
