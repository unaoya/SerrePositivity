module
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoin

/-! 二つの全 Hom パラメータと係数を変えた際の、任意次数の tensor cochain の比較。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R]

/-- 第一 primitive の輸送は、係数合成の可換正方形から従う。 -/
lemma dgGluingTensorRightPrimitive_transport
    {H H' J J' T T' U U' : Complex R} (p : ℤ)
    (a : H ⟶ H') (b : J ⟶ J') (c : T ⟶ T') (d : U ⟶ U')
    (h : Cochain H T p) (h' : Cochain H' T' p)
    (m : T ⊗ J ⟶ U) (n : T' ⊗ J' ⟶ U')
    (hh : (Cochain.ofHom a).comp h' (zero_add p) =
      h.comp (Cochain.ofHom c) (add_zero p))
    (hm : (c ⊗ₘ b) ≫ n = m ≫ d) :
    (Cochain.ofHom (a ⊗ₘ b)).comp
      (((tensorRightHom J' H' T').f p h').comp (Cochain.ofHom n) (add_zero p))
      (zero_add p) =
    (((tensorRightHom J H T).f p h).comp (Cochain.ofHom m) (add_zero p)).comp
      (Cochain.ofHom d) (add_zero p) := by
  rw [tensorHom_def, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_first_is_zero_cochain (Cochain.ofHom (H' ◁ b)),
    tensorRight_cochain_chain_naturality,
    ← Cochain.comp_assoc_of_first_is_zero_cochain (Cochain.ofHom (a ▷ J)),
    ← Cochain.comp_assoc_of_first_is_zero_cochain (Cochain.ofHom (a ▷ J))
      _ (Cochain.ofHom (T' ◁ b)),
    ← tensorRightHom_ofHom, ← tensorRightHom_cochain_comp, hh,
    tensorRightHom_cochain_comp, tensorRightHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain,
    ← Cochain.ofHom_comp, ← Cochain.ofHom_comp, ← Category.assoc, ← tensorHom_def, hm,
    Cochain.ofHom_comp, Cochain.comp_assoc_of_third_is_zero_cochain]

/-- 第二 primitive の輸送も、同じ全次数の cochain と係数正方形を使う。 -/
lemma dgGluingTensorLeftPrimitive_transport
    {H H' J J' T T' U U' : Complex R} (p : ℤ)
    (a : H ⟶ H') (b : J ⟶ J') (c : T ⟶ T') (d : U ⟶ U')
    (h : Cochain J T p) (h' : Cochain J' T' p)
    (m : H ⊗ T ⟶ U) (n : H' ⊗ T' ⟶ U')
    (hh : (Cochain.ofHom b).comp h' (zero_add p) =
      h.comp (Cochain.ofHom c) (add_zero p))
    (hm : (a ⊗ₘ c) ≫ n = m ≫ d) :
    (Cochain.ofHom (a ⊗ₘ b)).comp
      (((tensorLeftHom H' J' T').f p h').comp (Cochain.ofHom n) (add_zero p))
      (zero_add p) =
    (((tensorLeftHom H J T).f p h).comp (Cochain.ofHom m) (add_zero p)).comp
      (Cochain.ofHom d) (add_zero p) := by
  rw [tensorHom_def', Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_first_is_zero_cochain (Cochain.ofHom (a ▷ J')),
    ← tensorLeftHom_cochain_naturality,
    ← Cochain.comp_assoc_of_first_is_zero_cochain (Cochain.ofHom (H ◁ b)),
    ← Cochain.comp_assoc_of_first_is_zero_cochain (Cochain.ofHom (H ◁ b))
      _ (Cochain.ofHom (a ▷ T')),
    ← tensorLeftHom_ofHom, ← tensorLeftHom_cochain_comp, hh,
    tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain,
    ← Cochain.ofHom_comp, ← Cochain.ofHom_comp, ← Category.assoc, ← tensorHom_def', hm,
    Cochain.ofHom_comp, Cochain.comp_assoc_of_third_is_zero_cochain]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
