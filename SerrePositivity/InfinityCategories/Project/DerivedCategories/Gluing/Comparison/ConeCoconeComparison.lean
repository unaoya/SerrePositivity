module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ConeComparisons.CoconeSquare
/-! 正方形の cone と mapping cocone を交換する実比較鎖写像。 -/
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

lemma dgGluingConeCoconeFirst_boundary :
    δ (-1) 0 ((Cochain.ofHom (mappingCocone.fst μ)).comp
      (mappingCone.inl f) (zero_add (-1))) =
    Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeSquareMap f g μ ν h hh ≫
      mappingCocone.fst ν ≫ mappingCone.inr f) := by
  rw [δ_ofHom_comp, mappingCone.δ_inl, ← Cochain.ofHom_comp]
  congr 1
  simpa only [Category.assoc] using congrArg (fun t => t ≫ mappingCone.inr f)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeSquareMap_fst f g μ ν h hh).symm

def dgGluingConeCoconeFirst : mappingCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeSquareMap f g μ ν h hh) ⟶ mappingCone f :=
  mappingCone.desc _ ((Cochain.ofHom (mappingCocone.fst μ)).comp
    (mappingCone.inl f) (zero_add (-1)))
    (mappingCocone.fst ν ≫ mappingCone.inr f) (dgGluingConeCoconeFirst_boundary f g μ ν h hh)

def dgGluingConeCoconeSecond : Cochain (mappingCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeSquareMap f g μ ν h hh))
    (mappingCone g) (-1) :=
  mappingCone.descCochain _
    (- (mappingCocone.snd μ).comp (mappingCone.inl g) (by omega : -1 + -1 = -2))
    ((mappingCocone.snd ν).comp (Cochain.ofHom (mappingCone.inr g)) (add_zero (-1)))
    (by omega : -2 + 1 = -1)

lemma dgGluingConeCoconeSecond_boundary :
    δ (-1) 0 (dgGluingConeCoconeSecond f g μ ν h hh) +
      Cochain.ofHom (dgGluingConeCoconeFirst f g μ ν h hh ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMap f g μ ν h hh) = 0 := by
  have hs (A B : Complex R) (a : A ⟶ B) :
      δ (-1) 0 (mappingCocone.snd a) = - Cochain.ofHom (mappingCocone.fst a ≫ a) :=
    eq_neg_of_add_eq_zero_left (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCocone_snd_boundary a)
  unfold dgGluingConeCoconeSecond
  rw [mappingCone.δ_descCochain _ _ _ _ 0 (by omega)]
  rw [δ_neg, δ_comp _ _ _ 0 0 (-1) (by omega) (by omega) (by omega)]
  simp only [δ_comp_ofHom, mappingCone.δ_inl, hs, Int.negOnePow_zero,
    Int.negOnePow_neg, Int.negOnePow_one,
    one_smul, Units.neg_smul, Cochain.neg_comp, neg_neg]
  simp only [Cochain.ofHom_comp, dgGluingConeCoconeFirst, mappingCone.ofHom_desc,
    mappingCone.descCochain, Cochain.add_comp,
    Cochain.comp_assoc_of_third_is_zero_cochain,
    Cochain.comp_assoc_of_first_is_zero_cochain,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMap_inl]
  simp only [← Cochain.ofHom_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMap_inr,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquarePrimitive, Cochain.comp_add, Cochain.comp_neg]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeSquareMap f g μ ν h hh))
    (mappingCocone.snd ν) (Cochain.ofHom (mappingCone.inr g)) (add_zero (-1)),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeSquareMap_snd]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeSquarePrimitive, Cochain.sub_comp, Cochain.comp_sub,
    Cochain.comp_assoc_of_first_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp]
  abel

def dgGluingConeCoconeMap : mappingCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeSquareMap f g μ ν h hh) ⟶
    mappingCocone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMap f g μ ν h hh) :=
  mappingCocone.lift _ (dgGluingConeCoconeFirst f g μ ν h hh)
    (dgGluingConeCoconeSecond f g μ ν h hh)
    (dgGluingConeCoconeSecond_boundary f g μ ν h hh)

lemma dgGluingConeCoconeMap_fst : dgGluingConeCoconeMap f g μ ν h hh ≫
    mappingCocone.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMap f g μ ν h hh) = dgGluingConeCoconeFirst f g μ ν h hh :=
  mappingCocone.lift_fst _ _ _ _

lemma dgGluingConeCoconeMap_snd :
    (Cochain.ofHom (dgGluingConeCoconeMap f g μ ν h hh)).comp
      (mappingCocone.snd (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMap f g μ ν h hh)) (zero_add (-1)) =
        dgGluingConeCoconeSecond f g μ ν h hh := by
  apply Cochain.ext
  intro p q hpq
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, dgGluingConeCoconeMap]
  exact mappingCocone.lift_f_snd_v _ _ _ _ p q hpq

lemma dgGluingConeCoconeFirst_f (n : ℤ) :
    (dgGluingConeCoconeFirst f g μ ν h hh).f n =
      (mappingCone.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeSquareMap f g μ ν h hh)).val.v n (n + 1) rfl ≫
        (mappingCocone.fst μ).f (n + 1) ≫ (mappingCone.inl f).v (n + 1) n (by omega) +
      (mappingCone.snd (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeSquareMap f g μ ν h hh)).v n n (add_zero n) ≫
        (mappingCocone.fst ν).f n ≫ (mappingCone.inr f).f n := by
  rw [dgGluingConeCoconeFirst, mappingCone.desc_f _ _ _ _ n (n + 1) rfl]
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    HomologicalComplex.comp_f]

lemma dgGluingConeCoconeSecond_v (n : ℤ) :
    (dgGluingConeCoconeSecond f g μ ν h hh).v n (n - 1) (by omega) =
      - ((mappingCone.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeSquareMap f g μ ν h hh)).val.v n (n + 1) rfl ≫
        (mappingCocone.snd μ).v (n + 1) n (by omega) ≫
        (mappingCone.inl g).v n (n - 1) (by omega)) +
      (mappingCone.snd (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeSquareMap f g μ ν h hh)).v n n (add_zero n) ≫
        (mappingCocone.snd ν).v n (n - 1) (by omega) ≫ (mappingCone.inr g).f (n - 1) := by
  simp only [dgGluingConeCoconeSecond, mappingCone.descCochain, Cochain.add_v, Cochain.neg_v,
    Cochain.comp_v (n₁ := 1) (n₂ := -2) (n₁₂ := -1) _ _ (by omega) n (n + 1) (n - 1) rfl (by omega),
    Cochain.comp_v (n₁ := -1) (n₂ := -1) (n₁₂ := -2) _ _ (by omega) (n + 1) n (n - 1)
      (by omega) (by omega),
    Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
    Preadditive.comp_neg]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
