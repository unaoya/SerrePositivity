module
public import SerrePositivity.DifferentialGraded.Complexes.ConeMaps

/-! # coneの次数付き分裂と全次数作用

左包含はchain mapとは限らないが、shiftの符号を含めた次数付き作用と可換する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {P Q R S : Complex A}

lemma coneMapCochain_snd_v (f : P ⟶ Q) (g : R ⟶ S) {p : ℤ}
    (a : Homogeneous P R p) (b : Homogeneous Q S p)
    (i j : ℤ) (hij : i + p = j) :
    (coneMapCochain f g a b).v i j hij ≫ (mappingCone.snd g).v j j (add_zero j) =
      (mappingCone.snd f).v i i (add_zero i) ≫ b.v i j hij := by
  have h := Cochain.congr_v (coneMapCochain_snd f g a b) i j hij
  simpa only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v] using h

lemma coneMapCochain_inl_v (f : P ⟶ Q) (g : R ⟶ S) {p : ℤ}
    (a : Homogeneous P R p) (b : Homogeneous Q S p)
    (i j : ℤ) (hij : i + p = j) :
    (mappingCone.inl f).v (i + 1) i (by omega) ≫ (coneMapCochain f g a b).v i j hij =
      p.negOnePow • (a.v (i + 1) (j + 1) (by omega) ≫
        (mappingCone.inl g).v (j + 1) j (by omega)) := by
  rw [coneMapCochain_v]
  simp only [Preadditive.comp_add, Linear.comp_units_smul,
    mappingCone.inl_v_fst_v_assoc, mappingCone.inl_v_snd_v_assoc,
    zero_comp, add_zero]

/-- connecting mapの符号に合わせた、次数付き左section。 -/
def complexConeGradedSection (f : P ⟶ Q) (n : ℤ) :
    (P⟦(1 : ℤ)⟧).X n ⟶ (mappingCone f).X n :=
  -(mappingCone.inl f).v (n + 1) n (by omega)

/-- coneの右成分への次数付きretraction。 -/
def complexConeGradedRetraction (f : P ⟶ Q) (n : ℤ) :
    (mappingCone f).X n ⟶ Q.X n :=
  (mappingCone.snd f).v n n (add_zero n)

def complexConeGradedProjection (f : P ⟶ Q) (n : ℤ) :
    (mappingCone f).X n ⟶ (P⟦(1 : ℤ)⟧).X n :=
  -(mappingCone.fst f).val.v n (n + 1) rfl

lemma complexConeGradedProjection_eq_connecting (f : P ⟶ Q) (n : ℤ) :
    (mappingCone.triangle f).mor₃.f n = complexConeGradedProjection f n := by
  simp only [complexConeGradedProjection, SerrePositivity.coneTriangle_mor₃_f,
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_inv, Category.comp_id]

lemma complexConeGradedSection_connecting (f : P ⟶ Q) (n : ℤ) :
    complexConeGradedSection f n ≫ complexConeGradedProjection f n = 𝟙 _ := by
  simp only [complexConeGradedSection, complexConeGradedProjection,
    Preadditive.neg_comp, Preadditive.comp_neg,
    neg_neg, mappingCone.inl_v_fst_v]
  rfl

lemma complexConeGradedRetraction_inr (f : P ⟶ Q) (n : ℤ) :
    (mappingCone.inr f).f n ≫ complexConeGradedRetraction f n = 𝟙 _ :=
  mappingCone.inr_f_snd_v f n

lemma complexConeGradedSection_retraction (f : P ⟶ Q) (n : ℤ) :
    complexConeGradedSection f n ≫ complexConeGradedRetraction f n = 0 := by
  simp only [complexConeGradedSection, complexConeGradedRetraction,
    Preadditive.neg_comp, mappingCone.inl_v_snd_v, neg_zero]

lemma complexConeGraded_decomposition (f : P ⟶ Q) (n : ℤ) :
    complexConeGradedRetraction f n ≫ (mappingCone.inr f).f n +
      complexConeGradedProjection f n ≫ complexConeGradedSection f n = 𝟙 _ := by
  simp only [complexConeGradedSection, complexConeGradedRetraction,
    complexConeGradedProjection,
    Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
  exact (add_comm _ _).trans (mappingCone.id_X f n (n + 1) rfl)

lemma complexConeGradedSection_naturality (f : P ⟶ Q) (g : R ⟶ S) {p : ℤ}
    (a : Homogeneous P R p) (b : Homogeneous Q S p)
    (i j : ℤ) (hij : i + p = j) :
    complexConeGradedSection f i ≫ (coneMapCochain f g a b).v i j hij =
      ((shiftHom 1 P R).f p a).v i j hij ≫ complexConeGradedSection g j := by
  simp only [complexConeGradedSection, Preadditive.neg_comp, Preadditive.comp_neg]
  congr 1
  rw [coneMapCochain_inl_v]
  rw [shiftHom_v]
  simp only [one_mul, Linear.units_smul_comp]

end SerrePositivity.DifferentialGraded
