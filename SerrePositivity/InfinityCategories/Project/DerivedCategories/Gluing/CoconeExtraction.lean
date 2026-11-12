module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ConeCoconeIso
/-! cocone の実射影を保つ鎖写像から比較正方形を回収し、その cone を同定する。 -/
@[expose] public section
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
variable {R : Type u} [CommRing R] {P Q S T : Complex R}
  (μ : P ⟶ S) (ν : Q ⟶ T) (f : P ⟶ Q) (k : mappingCocone μ ⟶ mappingCocone ν)
  (hf : k ≫ mappingCocone.fst ν = mappingCocone.fst μ ≫ f)

lemma dgGluingCoconeInl_boundary : δ 0 1 (mappingCocone.inl μ) =
    -(Cochain.ofHom μ).comp (mappingCocone.inr μ).val (zero_add 1) := by
  have hi : mappingCocone.inl μ = mappingCocone.liftCochain μ
      (Cochain.ofHom (𝟙 P)) (0 : Cochain P S (-1)) (by omega) := by
    simp [mappingCocone.liftCochain, mappingCone.liftCochain, mappingCocone.inl]
  rw [hi, mappingCocone.δ_liftCochain _ _ _ _ 1 rfl]
  simp

def dgGluingCoconeExtractPrimitive : Cochain (mappingCocone μ) T (-1) :=
  (Cochain.ofHom k).comp (mappingCocone.snd ν) (zero_add (-1))

include hf in
lemma dgGluingCoconeExtractPrimitive_boundary : δ (-1) 0 (dgGluingCoconeExtractPrimitive μ ν k) =
    -Cochain.ofHom (mappingCocone.fst μ ≫ f ≫ ν) := by
  have hs : δ (-1) 0 (mappingCocone.snd ν) =
      -Cochain.ofHom (mappingCocone.fst ν ≫ ν) :=
    eq_neg_of_add_eq_zero_left (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCocone_snd_boundary ν)
  simp only [dgGluingCoconeExtractPrimitive, δ_ofHom_comp, hs, Cochain.comp_neg,
    ← Cochain.ofHom_comp]
  rw [← Category.assoc, hf, Category.assoc]

def dgGluingCoconeExtractBottomCochain : Cochain S T 0 :=
  (mappingCocone.inr μ).val.comp (dgGluingCoconeExtractPrimitive μ ν k) (by omega)

include hf in
lemma dgGluingCoconeExtractBottom_closed :
    δ 0 1 (dgGluingCoconeExtractBottomCochain μ ν k) = 0 := by
  have hz : (mappingCocone.inr μ).val.comp
      (Cochain.ofHom (mappingCocone.fst μ)) (add_zero 1) = 0 := by
    apply Cochain.ext
    intro p q hpq
    simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, Cochain.zero_v]
    exact mappingCocone.inr_v_fst_f μ p q hpq
  rw [dgGluingCoconeExtractBottomCochain, δ_comp _ _ _ 2 0 1 rfl rfl (by omega),
    dgGluingCoconeExtractPrimitive_boundary μ ν f k hf]
  simp only [Cocycle.δ_eq_zero, Cochain.zero_comp, smul_zero, add_zero,
    Cochain.comp_neg, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_third_is_zero_cochain, hz, Cochain.zero_comp, neg_zero]

def dgGluingCoconeExtractBottom : S ⟶ T :=
  (Cocycle.mk (dgGluingCoconeExtractBottomCochain μ ν k) 1 rfl
    (dgGluingCoconeExtractBottom_closed μ ν f k hf)).homOf

lemma dgGluingCoconeExtractBottom_cochain :
    Cochain.ofHom (dgGluingCoconeExtractBottom μ ν f k hf) =
      dgGluingCoconeExtractBottomCochain μ ν k :=
  Cocycle.cochain_ofHom_homOf_eq_coe _

def dgGluingCoconeExtractHomotopy : Cochain P T (-1) :=
  -(mappingCocone.inl μ).comp (dgGluingCoconeExtractPrimitive μ ν k) (zero_add (-1))

lemma dgGluingCoconeInl_fst : (mappingCocone.inl μ).comp
    (Cochain.ofHom (mappingCocone.fst μ)) (zero_add 0) = Cochain.ofHom (𝟙 P) := by
  apply Cochain.ext₀
  intro n
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    mappingCocone.inl_v_fst_f, HomologicalComplex.id_f]

lemma dgGluingCoconeExtractHomotopy_boundary : δ (-1) 0 (dgGluingCoconeExtractHomotopy μ ν k) +
    Cochain.ofHom (μ ≫ dgGluingCoconeExtractBottom μ ν f k hf - f ≫ ν) = 0 := by
  rw [dgGluingCoconeExtractHomotopy, δ_neg, δ_comp _ _ _ 1 0 0 (by omega) rfl (by omega),
    dgGluingCoconeInl_boundary, dgGluingCoconeExtractPrimitive_boundary μ ν f k hf]
  simp only [Cochain.comp_neg, Cochain.neg_comp, Int.negOnePow_neg,
    Int.negOnePow_one, Units.neg_smul, one_smul, neg_neg,
    Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain
    (mappingCocone.inl μ) (Cochain.ofHom (mappingCocone.fst μ))
    ((Cochain.ofHom f).comp (Cochain.ofHom ν) (zero_add 0)) (zero_add 0),
    dgGluingCoconeInl_fst]
  simp only [Cochain.ofHom_sub, Cochain.ofHom_comp, dgGluingCoconeExtractBottom_cochain,
    dgGluingCoconeExtractBottomCochain, Cochain.id_comp]
  abel

lemma dgGluingCoconeExtractPrimitive_recovery :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeSquarePrimitive (dgGluingCoconeExtractBottom μ ν f k hf) μ
      (dgGluingCoconeExtractHomotopy μ ν k) =
      dgGluingCoconeExtractPrimitive μ ν k := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeSquarePrimitive, dgGluingCoconeExtractBottom_cochain,
    dgGluingCoconeExtractBottomCochain,
    dgGluingCoconeExtractHomotopy, Cochain.comp_neg, sub_neg_eq_add]
  apply Cochain.ext
  intro p q hpq
  simp only [Cochain.add_v, Cochain.zero_cochain_comp_v,
    Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
    Cochain.comp_v (n₁ := 1) (n₂ := -1) (n₁₂ := 0) _ _ (by omega)
      q p q (by omega) hpq]
  rw [← Category.assoc, ← Category.assoc, ← Preadditive.add_comp, add_comm,
    mappingCocone.id_X μ p q hpq, Category.id_comp]

lemma dgGluingCoconeExtractMap_recovery :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeSquareMap f (dgGluingCoconeExtractBottom μ ν f k hf) μ ν
      (dgGluingCoconeExtractHomotopy μ ν k)
      (dgGluingCoconeExtractHomotopy_boundary μ ν f k hf) = k := by
  apply HomologicalComplex.hom_ext
  intro n
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCocone_X_ext ν n
  · have he := congrArg (fun t => t.f n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeSquareMap_fst f (dgGluingCoconeExtractBottom μ ν f k hf) μ ν
        (dgGluingCoconeExtractHomotopy μ ν k)
        (dgGluingCoconeExtractHomotopy_boundary μ ν f k hf))
    have hk := congrArg (fun t => t.f n) hf
    simpa only [HomologicalComplex.comp_f] using he.trans hk.symm
  · have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeSquareMap_snd f (dgGluingCoconeExtractBottom μ ν f k hf) μ ν
      (dgGluingCoconeExtractHomotopy μ ν k)
        (dgGluingCoconeExtractHomotopy_boundary μ ν f k hf)
    rw [dgGluingCoconeExtractPrimitive_recovery] at he
    have hv := Cochain.congr_v he n (n - 1) (by omega)
    dsimp only [dgGluingCoconeExtractPrimitive] at hv
    erw [Cochain.zero_cochain_comp_v, Cochain.zero_cochain_comp_v] at hv
    exact hv

def dgGluingCoconeExtractConeArrow :
    mappingCone f ⟶ mappingCone (dgGluingCoconeExtractBottom μ ν f k hf) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMap f (dgGluingCoconeExtractBottom μ ν f k hf) μ ν
      (dgGluingCoconeExtractHomotopy μ ν k)
    (dgGluingCoconeExtractHomotopy_boundary μ ν f k hf)

def dgGluingCoconeExtractConeIso :
    mappingCone k ≅ mappingCocone (dgGluingCoconeExtractConeArrow μ ν f k hf) :=
  eqToIso (congrArg (fun a : mappingCocone μ ⟶ mappingCocone ν => mappingCone a)
    (dgGluingCoconeExtractMap_recovery μ ν f k hf).symm) ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeCoconeIso f (dgGluingCoconeExtractBottom μ ν f k hf) μ ν
      (dgGluingCoconeExtractHomotopy μ ν k)
      (dgGluingCoconeExtractHomotopy_boundary μ ν f k hf)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
