module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomComplex

/-! 指定比較ホモトピーを保持する cone 間の実鎖写像。第三成分を捨てずに行列の非対角項へ移す。 -/
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
def dgGluingConeSquarePrimitive : Cochain P (mappingCone g) (-1) :=
  (Cochain.ofHom μ).comp (mappingCone.inl g) (zero_add (-1)) +
    h.comp (Cochain.ofHom (mappingCone.inr g)) (add_zero (-1))
include hh in
lemma dgGluingConeSquarePrimitive_boundary :
    δ (-1) 0 (dgGluingConeSquarePrimitive g μ h) =
      Cochain.ofHom (f ≫ ν ≫ mappingCone.inr g) := by
  have hh' : δ (-1) 0 h = Cochain.ofHom (f ≫ ν - μ ≫ g) := by
    have ht := eq_neg_of_add_eq_zero_left hh
    simpa only [← Cochain.ofHom_neg, neg_sub] using ht
  simp only [dgGluingConeSquarePrimitive, δ_add, δ_ofHom_comp, δ_comp_ofHom,
    mappingCone.δ_inl, hh', ← Cochain.ofHom_comp, ← Cochain.ofHom_add,
    Preadditive.sub_comp, Category.assoc]
  congr 1
  abel

def dgGluingConeSquareMap : mappingCone f ⟶ mappingCone g :=
  mappingCone.desc f (dgGluingConeSquarePrimitive g μ h) (ν ≫ mappingCone.inr g)
    (dgGluingConeSquarePrimitive_boundary f g μ ν h hh)

lemma dgGluingConeSquareMap_inr :
    mappingCone.inr f ≫ dgGluingConeSquareMap f g μ ν h hh = ν ≫ mappingCone.inr g :=
  mappingCone.inr_desc _ _ _ _
lemma dgGluingConeSquareMap_inl :
    (mappingCone.inl f).comp (Cochain.ofHom (dgGluingConeSquareMap f g μ ν h hh)) (add_zero (-1)) =
      dgGluingConeSquarePrimitive g μ h := mappingCone.inl_desc _ _ _ _
lemma dgGluingConeSquareMap_f (n : ℤ) :
    (dgGluingConeSquareMap f g μ ν h hh).f n =
      (mappingCone.fst f).val.v n (n + 1) rfl ≫
        (μ.f (n + 1) ≫ (mappingCone.inl g).v (n + 1) n (by omega) +
          h.v (n + 1) n (by omega) ≫ (mappingCone.inr g).f n) +
      (mappingCone.snd f).v n n (add_zero n) ≫ ν.f n ≫ (mappingCone.inr g).f n := by
  rw [dgGluingConeSquareMap, mappingCone.desc_f f _ _ _ n (n + 1) rfl]
  simp only [dgGluingConeSquarePrimitive, Cochain.add_v, Cochain.zero_cochain_comp_v,
    Cochain.comp_zero_cochain_v, Cochain.ofHom_v, HomologicalComplex.comp_f]

lemma dgGluingConeSquareMap_zero (comm : f ≫ ν = μ ≫ g)
    (hh0 : δ (-1) 0 (0 : Cochain P T (-1)) + Cochain.ofHom (μ ≫ g - f ≫ ν) = 0) :
    dgGluingConeSquareMap f g μ ν 0 hh0 = mappingCone.map f g μ ν comm := by
  apply HomologicalComplex.hom_ext
  intro n
  apply mappingCone.ext_from f (n + 1) n rfl
  · simp only [dgGluingConeSquareMap, mappingCone.inl_v_desc_f, dgGluingConeSquarePrimitive,
      Cochain.add_v, Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v,
      Cochain.ofHom_v, Cochain.zero_v, zero_comp, add_zero, mappingCone.map]
  · simp only [dgGluingConeSquareMap, mappingCone.inr_f_desc_f, mappingCone.map]

/-- 指定比較ホモトピーを保持する cone 写像の全行列 cochain。 -/
def dgGluingConeSquareMatrix : Cochain (mappingCone f) (mappingCone g) 0 :=
  (((mappingCone.fst f).val.comp (Cochain.ofHom μ) (add_zero 1)).comp
    (mappingCone.inl g) (add_neg_cancel 1) +
  ((mappingCone.snd f).comp (Cochain.ofHom ν) (add_zero 0)).comp
    (Cochain.ofHom (mappingCone.inr g)) (add_zero 0)) +
  ((mappingCone.fst f).val.comp h (add_neg_cancel 1)).comp
    (Cochain.ofHom (mappingCone.inr g)) (add_zero 0)

/-- 三項行列は構成した実 cone 写像そのもの。 -/
lemma dgGluingConeSquareMatrix_eq :
    dgGluingConeSquareMatrix f g μ ν h =
      Cochain.ofHom (dgGluingConeSquareMap f g μ ν h hh) := by
  apply Cochain.ext₀
  intro n
  simp only [dgGluingConeSquareMatrix, Cochain.add_v,
    Cochain.comp_v (n₁ := 1) (n₂ := -1) _ _ (add_neg_cancel 1)
      n (n + 1) n rfl (by omega),
    Cochain.comp_zero_cochain_v, Cochain.ofHom_v, dgGluingConeSquareMap_f,
    Preadditive.comp_add, Category.assoc]
  exact add_right_comm _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
