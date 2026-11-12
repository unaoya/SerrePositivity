module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ComplexTwoEndpointPath

/-! 二つの端点を全次数で同時に持ち上げる、元の cocone 包含による指定切断。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R] (Q : Complex R) (n : ℤ)

def dgGluingComplexPathEndpointSection : (Q ⊞ Q).X n ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPath Q).X n :=
  (biprod.fst : Q ⊞ Q ⟶ Q).f n ≫ (biprod.inl : Q ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPath Q).f n +
    ((biprod.snd : Q ⊞ Q ⟶ Q).f n - (biprod.fst : Q ⊞ Q ⟶ Q).f n) ≫
      (mappingCocone.inl (𝟙 Q)).v n n (add_zero n) ≫
        (biprod.inr : mappingCocone (𝟙 Q) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPath Q).f n

lemma dgGluingComplexPathEndpointSection_projections :
    dgGluingComplexPathEndpointSection Q n ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathStart Q).f n =
        (biprod.fst : Q ⊞ Q ⟶ Q).f n ∧
      dgGluingComplexPathEndpointSection Q n ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEnd Q).f n =
        (biprod.snd : Q ⊞ Q ⟶ Q).f n := by
  have hs₀ : (biprod.inl : Q ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPath Q).f n ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathStart Q).f n = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f]
    simp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathStart, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanLeft]
  have hs₁ : (biprod.inr : mappingCocone (𝟙 Q) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPath Q).f n ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathStart Q).f n = 0 := by
    rw [← HomologicalComplex.comp_f]
    simp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathStart, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanLeft]
  have he₀ : (biprod.inl : Q ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPath Q).f n ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEnd Q).f n = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f]
    simp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEnd, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanRight]
  have he₁ : (biprod.inr : mappingCocone (𝟙 Q) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPath Q).f n ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEnd Q).f n = (mappingCocone.fst (𝟙 Q)).f n := by
    rw [← HomologicalComplex.comp_f]
    simp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEnd, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanRight]
  constructor
  · simp only [dgGluingComplexPathEndpointSection, Preadditive.add_comp, Category.assoc,
      hs₀, hs₁, Category.comp_id, comp_zero, add_zero]
  · simp only [dgGluingComplexPathEndpointSection, Preadditive.add_comp, Category.assoc,
      he₀, he₁, Category.comp_id]
    rw [mappingCocone.inl_v_fst_f, Category.comp_id]
    abel

lemma dgGluingComplexPathEndpointSection_endpoints :
    dgGluingComplexPathEndpointSection Q n ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEndpoints Q).f n = 𝟙 _ := by
  have htotal := congrArg (fun m : Q ⊞ Q ⟶ Q ⊞ Q => m.f n)
    (biprod.total (X := Q) (Y := Q))
  change (biprod.fst : Q ⊞ Q ⟶ Q).f n ≫ (biprod.inl : Q ⟶ Q ⊞ Q).f n +
    (biprod.snd : Q ⊞ Q ⟶ Q).f n ≫ (biprod.inr : Q ⟶ Q ⊞ Q).f n = 𝟙 _ at htotal
  have hs : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEndpoints Q).f n ≫ (biprod.fst : Q ⊞ Q ⟶ Q).f n =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathStart Q).f n := by
    rw [← HomologicalComplex.comp_f, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEndpoints, biprod.lift_fst]
  have he : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEndpoints Q).f n ≫ (biprod.snd : Q ⊞ Q ⟶ Q).f n =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEnd Q).f n := by
    rw [← HomologicalComplex.comp_f, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEndpoints, biprod.lift_snd]
  have hl : (dgGluingComplexPathEndpointSection Q n ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEndpoints Q).f n) ≫
      (biprod.fst : Q ⊞ Q ⟶ Q).f n = (biprod.fst : Q ⊞ Q ⟶ Q).f n := by
    rw [Category.assoc, hs, (dgGluingComplexPathEndpointSection_projections Q n).1]
  have hr : (dgGluingComplexPathEndpointSection Q n ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEndpoints Q).f n) ≫
      (biprod.snd : Q ⊞ Q ⟶ Q).f n = (biprod.snd : Q ⊞ Q ⟶ Q).f n := by
    rw [Category.assoc, he, (dgGluingComplexPathEndpointSection_projections Q n).2]
  calc
    _ = dgGluingComplexPathEndpointSection Q n ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEndpoints Q).f n ≫
        ((biprod.fst : Q ⊞ Q ⟶ Q).f n ≫ (biprod.inl : Q ⟶ Q ⊞ Q).f n +
          (biprod.snd : Q ⊞ Q ⟶ Q).f n ≫ (biprod.inr : Q ⟶ Q ⊞ Q).f n) := by
      rw [htotal, Category.comp_id]
    _ = _ := by
      simp only [Preadditive.comp_add, ← Category.assoc]
      rw [hl, hr, htotal]

lemma dgGluingComplexPathEndpoints_surjective :
    Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEndpoints Q).f n) := by
  intro y
  exact ⟨dgGluingComplexPathEndpointSection Q n y,
    ConcreteCategory.congr_hom (dgGluingComplexPathEndpointSection_endpoints Q n) y⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
