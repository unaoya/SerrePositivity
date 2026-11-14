module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.ConeCoconeComparison
public import SerrePositivity.DifferentialGraded.Complexes.Cone
/-! 二重 cone の比較は、全整数次数の四成分を交換する実鎖同型。 -/
@[expose] public section
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
variable {R : Type u} [CommRing R] {P Q S T : Complex R}
  (f : P ⟶ Q) (g : S ⟶ T) (μ : P ⟶ S) (ν : Q ⟶ T)
  (h : Cochain P T (-1))
  (hh : δ (-1) 0 h + Cochain.ofHom (μ ≫ g - f ≫ ν) = 0)
local notation "κ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeSquareMap f g μ ν h hh
local notation "ℓ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMap f g μ ν h hh
local notation "e" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeCoconeMap f g μ ν h hh

lemma dgGluingConeCoconeMap_fst_fst (n : ℤ) :
    (e).f n ≫ (mappingCocone.fst ℓ).f n ≫ (mappingCone.fst f).val.v n (n + 1) rfl =
      (mappingCone.fst κ).val.v n (n + 1) rfl ≫ (mappingCocone.fst μ).f (n + 1) := by
  have hf := congrArg (fun t => t.f n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeCoconeMap_fst f g μ ν h hh)
  simp only [HomologicalComplex.comp_f] at hf
  rw [← Category.assoc, hf, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeCoconeFirst_f]
  simp only [Preadditive.add_comp, Category.assoc, mappingCone.inl_v_fst_v,
    mappingCone.inr_f_fst_v, Category.comp_id, comp_zero, add_zero]

lemma dgGluingConeCoconeMap_fst_snd (n : ℤ) :
    (e).f n ≫ (mappingCocone.fst ℓ).f n ≫ (mappingCone.snd f).v n n (add_zero n) =
      (mappingCone.snd κ).v n n (add_zero n) ≫ (mappingCocone.fst ν).f n := by
  have hf := congrArg (fun t => t.f n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeCoconeMap_fst f g μ ν h hh)
  simp only [HomologicalComplex.comp_f] at hf
  rw [← Category.assoc, hf, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeCoconeFirst_f]
  simp only [Preadditive.add_comp, Category.assoc, mappingCone.inl_v_snd_v,
    mappingCone.inr_f_snd_v, Category.comp_id, comp_zero, zero_add]

lemma dgGluingConeCoconeMap_snd_fst (n : ℤ) :
    (e).f n ≫ (mappingCocone.snd ℓ).v n (n - 1) (by omega) ≫
        (mappingCone.fst g).val.v (n - 1) n (by omega) =
      - ((mappingCone.fst κ).val.v n (n + 1) rfl ≫
        (mappingCocone.snd μ).v (n + 1) n (by omega)) := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeCoconeMap, mappingCocone.lift_f_snd_v,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeCoconeSecond_v]
  simp only [Preadditive.add_comp, Preadditive.neg_comp, Category.assoc,
    mappingCone.inl_v_fst_v, mappingCone.inr_f_fst_v,
    Category.comp_id, comp_zero, add_zero]

lemma dgGluingConeCoconeMap_snd_snd (n : ℤ) :
    (e).f n ≫ (mappingCocone.snd ℓ).v n (n - 1) (by omega) ≫
        (mappingCone.snd g).v (n - 1) (n - 1) (add_zero (n - 1)) =
      (mappingCone.snd κ).v n n (add_zero n) ≫
        (mappingCocone.snd ν).v n (n - 1) (by omega) := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeCoconeMap, mappingCocone.lift_f_snd_v,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeCoconeSecond_v]
  simp only [Preadditive.add_comp, Preadditive.neg_comp, Category.assoc,
    mappingCone.inl_v_snd_v, mappingCone.inr_f_snd_v,
    Category.comp_id, comp_zero, neg_zero, zero_add]

def dgGluingCoconeElementMk {A B : Complex R} (a : A ⟶ B) (n m : ℤ) (hm : n + -1 = m)
    (x : A.X n) (y : B.X m) : (mappingCocone a).X n :=
  (mappingCocone.inl a).v n n (add_zero n) x +
    (mappingCocone.inr a).val.v m n (by omega) y

lemma dgGluingCoconeElementMk_fst {A B : Complex R} (a : A ⟶ B) (n m : ℤ) (hm : n + -1 = m)
    (x : A.X n) (y : B.X m) :
    (mappingCocone.fst a).f n (dgGluingCoconeElementMk a n m hm x y) = x := by
  simp only [dgGluingCoconeElementMk, map_add, ← ModuleCat.comp_apply,
    mappingCocone.inl_v_fst_f, mappingCocone.inr_v_fst_f,
    ModuleCat.id_apply, ModuleCat.hom_zero, LinearMap.zero_apply, add_zero]

lemma dgGluingCoconeElementMk_snd {A B : Complex R} (a : A ⟶ B) (n m : ℤ) (hm : n + -1 = m)
    (x : A.X n) (y : B.X m) :
    (mappingCocone.snd a).v n m hm (dgGluingCoconeElementMk a n m hm x y) = y := by
  simp only [dgGluingCoconeElementMk, map_add, ← ModuleCat.comp_apply,
    mappingCocone.inl_v_snd_v, mappingCocone.inr_v_snd_v,
    ModuleCat.id_apply, ModuleCat.hom_zero, LinearMap.zero_apply, zero_add]

lemma dgGluingCoconeElementMk_eta {A B : Complex R} (a : A ⟶ B) (n m : ℤ) (hm : n + -1 = m)
    (z : (mappingCocone a).X n) :
    dgGluingCoconeElementMk a n m hm ((mappingCocone.fst a).f n z)
      ((mappingCocone.snd a).v n m hm z) = z := by
  have ht := congrArg (fun t => t z) (mappingCocone.id_X a n m hm)
  simpa only [dgGluingCoconeElementMk, ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply,
    ModuleCat.id_apply] using ht

lemma dgGluingCoconeElement_ext {A B : Complex R} (a : A ⟶ B) (n m : ℤ) (hm : n + -1 = m)
    {z w : (mappingCocone a).X n}
    (hf : (mappingCocone.fst a).f n z = (mappingCocone.fst a).f n w)
    (hs : (mappingCocone.snd a).v n m hm z = (mappingCocone.snd a).v n m hm w) : z = w := by
  rw [← dgGluingCoconeElementMk_eta a n m hm z, ← dgGluingCoconeElementMk_eta a n m hm w, hf, hs]

lemma dgGluingConeElement_extIndices {A B : Complex R} (a : A ⟶ B) (n m : ℤ) (hm : n + 1 = m)
    {z w : (mappingCone a).X n}
    (hf : (mappingCone.fst a).val.v n m hm z = (mappingCone.fst a).val.v n m hm w)
    (hs : (mappingCone.snd a).v n n (add_zero n) z =
      (mappingCone.snd a).v n n (add_zero n) w) : z = w := by
  have ez := congrArg (fun t => t z) (mappingCone.id_X a n m hm)
  have ew := congrArg (fun t => t w) (mappingCone.id_X a n m hm)
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply,
    ModuleCat.id_apply] at ez ew
  rw [← ez, ← ew, hf, hs]

lemma dgGluingConeCoconeMap_injective (n : ℤ) : Function.Injective ((e).f n) := by
  intro z w hz
  apply complexConeElement_ext R κ n
  · apply dgGluingCoconeElement_ext μ (n + 1) n (by omega)
    · have ht := congrArg (fun v =>
        (mappingCone.fst f).val.v n (n + 1) rfl ((mappingCocone.fst ℓ).f n v)) hz
      simpa only [← ModuleCat.comp_apply, Category.assoc, dgGluingConeCoconeMap_fst_fst] using ht
    · have ht := congrArg (fun v =>
        (mappingCone.fst g).val.v (n - 1) n (by omega)
          ((mappingCocone.snd ℓ).v n (n - 1) (by omega) v)) hz
      simpa only [← ModuleCat.comp_apply, Category.assoc, dgGluingConeCoconeMap_snd_fst,
        ModuleCat.hom_neg, LinearMap.neg_apply, neg_inj] using ht
  · apply dgGluingCoconeElement_ext ν n (n - 1) (by omega)
    · have ht := congrArg (fun v =>
        (mappingCone.snd f).v n n (add_zero n) ((mappingCocone.fst ℓ).f n v)) hz
      simpa only [← ModuleCat.comp_apply, Category.assoc, dgGluingConeCoconeMap_fst_snd] using ht
    · have ht := congrArg (fun v =>
        (mappingCone.snd g).v (n - 1) (n - 1) (add_zero (n - 1))
          ((mappingCocone.snd ℓ).v n (n - 1) (by omega) v)) hz
      simpa only [← ModuleCat.comp_apply, Category.assoc, dgGluingConeCoconeMap_snd_snd] using ht

lemma dgGluingConeCoconeMap_surjective (n : ℤ) : Function.Surjective ((e).f n) := by
  intro z
  let a := (mappingCocone.fst ℓ).f n z
  let b := (mappingCocone.snd ℓ).v n (n - 1) (by omega) z
  let x := dgGluingCoconeElementMk μ (n + 1) n (by omega)
    ((mappingCone.fst f).val.v n (n + 1) rfl a)
    (- (mappingCone.fst g).val.v (n - 1) n (by omega) b)
  let y := dgGluingCoconeElementMk ν n (n - 1) (by omega)
    ((mappingCone.snd f).v n n (add_zero n) a)
    ((mappingCone.snd g).v (n - 1) (n - 1) (add_zero (n - 1)) b)
  refine ⟨complexConeElementMk R κ n x y, ?_⟩
  apply dgGluingCoconeElement_ext ℓ n (n - 1) (by omega)
  · apply complexConeElement_ext R f n
    · simp only [← ModuleCat.comp_apply, Category.assoc, dgGluingConeCoconeMap_fst_fst]
      simp only [ModuleCat.comp_apply,
        complexConeElementMk_fst, x, dgGluingCoconeElementMk_fst, a]
    · simp only [← ModuleCat.comp_apply, Category.assoc, dgGluingConeCoconeMap_fst_snd]
      simp only [ModuleCat.comp_apply,
        complexConeElementMk_snd, y, dgGluingCoconeElementMk_fst, a]
  · apply dgGluingConeElement_extIndices g (n - 1) n (by omega)
    · simp only [← ModuleCat.comp_apply, Category.assoc, dgGluingConeCoconeMap_snd_fst]
      simp only [ModuleCat.hom_neg, LinearMap.neg_apply, ModuleCat.comp_apply,
        complexConeElementMk_fst, x, dgGluingCoconeElementMk_snd, neg_neg, b]
    · simp only [← ModuleCat.comp_apply, Category.assoc, dgGluingConeCoconeMap_snd_snd]
      simp only [ModuleCat.comp_apply,
        complexConeElementMk_snd, y, dgGluingCoconeElementMk_snd, b]

lemma dgGluingConeCoconeMap_isIso : IsIso (e) := by
  have (n : ℤ) : IsIso ((e).f n) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      ⟨dgGluingConeCoconeMap_injective f g μ ν h hh n,
        dgGluingConeCoconeMap_surjective f g μ ν h hh n⟩
  exact HomologicalComplex.Hom.isIso_of_components _

/-- ホモトピー可換な正方形の cone と mapping cocone を交換する鎖同型。 -/
def dgGluingConeCoconeIso : mappingCone κ ≅ mappingCocone ℓ := by
  letI := dgGluingConeCoconeMap_isIso f g μ ν h hh
  exact asIso (e)

lemma dgGluingConeCoconeIso_hom :
    (dgGluingConeCoconeIso f g μ ν h hh).hom = e := rfl

lemma dgGluingConeCoconeMap_inr_fst : mappingCone.inr κ ≫ e ≫ mappingCocone.fst ℓ =
    mappingCocone.fst ν ≫ mappingCone.inr f := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeCoconeMap_fst, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeCoconeFirst, mappingCone.inr_desc]

lemma dgGluingConeCoconeMap_inr_snd : (Cochain.ofHom (mappingCone.inr κ ≫ e)).comp
    (mappingCocone.snd ℓ) (zero_add (-1)) =
    (mappingCocone.snd ν).comp (Cochain.ofHom (mappingCone.inr g)) (add_zero (-1)) := by
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeCoconeMap_snd, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeCoconeSecond, mappingCone.inr_descCochain]

lemma dgGluingConeCoconeMap_inr : mappingCone.inr κ ≫ e =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap ν ℓ (mappingCone.inr f) (mappingCone.inr g)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMap_inr f g μ ν h hh).symm := by
  apply HomologicalComplex.hom_ext
  intro n
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCocone_X_ext ℓ n
  · have ht := congrArg (fun t => t.f n) (dgGluingConeCoconeMap_inr_fst f g μ ν h hh)
    simpa only [HomologicalComplex.comp_f, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_f_fst_f] using ht
  · have ht := Cochain.congr_v (dgGluingConeCoconeMap_inr_snd f g μ ν h hh) n (n - 1) (by omega)
    simpa only [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v,
      Cochain.ofHom_v, HomologicalComplex.comp_f, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_f_snd_v] using ht

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
