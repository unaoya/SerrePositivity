module
public import SerrePositivity.DifferentialGraded.Complexes.ConeMaps
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

/-! # 指定された合成とcone射に対する八面体の複体比較

加群の評価は合成とcone射に命題的に一致する。その等式を入力に保持する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {K L P : Complex A}

/-- cone(g)と、指定されたcone(f)→cone(θ)のconeとの既存ホモトピー同値。 -/
def complexConeCompHomotopyEquiv (f : K ⟶ L) (g : L ⟶ P) (θ : K ⟶ P)
    (hθ : θ = f ≫ g) (χ : mappingCone f ⟶ mappingCone θ)
    (hχ : χ = mappingCone.map f θ (𝟙 K) g (by rw [hθ, Category.id_comp])) :
    HomotopyEquiv (mappingCone g) (mappingCone χ) := by
  subst θ
  subst χ
  exact mappingConeCompHomotopyEquiv f g

lemma complexConeComp_hom_cochain (f : K ⟶ L) (g : L ⟶ P) (θ : K ⟶ P)
    (hθ : θ = f ≫ g) (χ : mappingCone f ⟶ mappingCone θ)
    (hχ : χ = mappingCone.map f θ (𝟙 K) g (by rw [hθ, Category.id_comp])) :
    Cochain.ofHom (complexConeCompHomotopyEquiv f g θ hθ χ hχ).hom =
      mappingCone.liftCochain χ
        ((mappingCone.fst g).val.comp (Cochain.ofHom (mappingCone.inr f)) (add_zero 1))
        (mappingCone.descCochain g 0 (Cochain.ofHom (mappingCone.inr θ)) (neg_add_cancel 1))
        (zero_add 1) := by
  subst θ
  subst χ
  simp only [complexConeCompHomotopyEquiv, mappingConeCompHomotopyEquiv,
    MappingConeCompHomotopyEquiv.hom, mappingConeCompTriangle, Pretriangulated.Triangle.mk,
    mappingCone.ofHom_lift, mappingCone.descCocycle_coe,
    mappingCone.descCochain, Cocycle.coe_zero, Cochain.comp_zero, add_zero]

lemma complexConeComp_inv_cochain (f : K ⟶ L) (g : L ⟶ P) (θ : K ⟶ P)
    (hθ : θ = f ≫ g) (χ : mappingCone f ⟶ mappingCone θ)
    (hχ : χ = mappingCone.map f θ (𝟙 K) g (by rw [hθ, Category.id_comp])) :
    Cochain.ofHom (complexConeCompHomotopyEquiv f g θ hθ χ hχ).inv =
      mappingCone.descCochain χ ((mappingCone.snd f).comp (mappingCone.inl g) (zero_add (-1)))
        (mappingCone.descCochain θ ((Cochain.ofHom f).comp (mappingCone.inl g) (zero_add (-1)))
          (Cochain.ofHom (mappingCone.inr g)) (neg_add_cancel 1)) (neg_add_cancel 1) := by
  subst θ
  subst χ
  simp only [complexConeCompHomotopyEquiv, mappingConeCompHomotopyEquiv,
    MappingConeCompHomotopyEquiv.inv, mappingConeCompTriangle, Pretriangulated.Triangle.mk,
    mappingCone.ofHom_desc]

lemma complexConeComp_hom_inv (f : K ⟶ L) (g : L ⟶ P) (θ : K ⟶ P)
    (hθ : θ = f ≫ g) (χ : mappingCone f ⟶ mappingCone θ)
    (hχ : χ = mappingCone.map f θ (𝟙 K) g (by rw [hθ, Category.id_comp])) :
    (complexConeCompHomotopyEquiv f g θ hθ χ hχ).hom ≫
      (complexConeCompHomotopyEquiv f g θ hθ χ hχ).inv = 𝟙 _ := by
  subst θ
  subst χ
  exact mappingConeCompHomotopyEquiv_hom_inv_id f g

lemma complexConeComp_inv_hom_boundary (f : K ⟶ L) (g : L ⟶ P) (θ : K ⟶ P)
    (hθ : θ = f ≫ g) (χ : mappingCone f ⟶ mappingCone θ)
    (hχ : χ = mappingCone.map f θ (𝟙 K) g (by rw [hθ, Category.id_comp])) :
    δ (-1) 0 (-((mappingCone.snd χ).comp ((mappingCone.fst θ).val.comp
      ((mappingCone.inl f).comp (mappingCone.inl χ) (by decide))
        (show (1 : ℤ) + (-2) = -1 by decide)) (zero_add (-1)))) =
      Cochain.ofHom ((complexConeCompHomotopyEquiv f g θ hθ χ hχ).inv ≫
        (complexConeCompHomotopyEquiv f g θ hθ χ hχ).hom) - Cochain.ofHom (𝟙 _) := by
  subst θ
  subst χ
  let H := (mappingConeCompHomotopyEquiv f g).homotopyInvHomId
  have hc : ((Cochain.equivHomotopy _ _) H).val =
      -((mappingCone.snd _).comp ((mappingCone.fst (f ≫ g)).val.comp
        ((mappingCone.inl f).comp (mappingCone.inl _) (by decide))
          (show (1 : ℤ) + (-2) = -1 by decide)) (zero_add (-1))) := by
    simp only [H, mappingConeCompHomotopyEquiv, MappingConeCompHomotopyEquiv.homotopyInvHomId,
      Equiv.apply_symm_apply]
  have hd := ((Cochain.equivHomotopy _ _) H).property
  rw [hc] at hd
  exact (eq_sub_iff_add_eq).2 hd.symm

lemma complexConeComp_inr_inv (f : K ⟶ L) (g : L ⟶ P) (θ : K ⟶ P)
    (hθ : θ = f ≫ g) (χ : mappingCone f ⟶ mappingCone θ)
    (hχ : χ = mappingCone.map f θ (𝟙 K) g (by rw [hθ, Category.id_comp])) :
    mappingCone.inr χ ≫ (complexConeCompHomotopyEquiv f g θ hθ χ hχ).inv =
      mappingCone.map θ g f (𝟙 P) (by rw [hθ, Category.comp_id]) := by
  subst θ
  subst χ
  exact mappingConeCompHomotopyEquiv_comm₁ f g

lemma complexConeComp_hom_connecting (f : K ⟶ L) (g : L ⟶ P) (θ : K ⟶ P)
    (hθ : θ = f ≫ g) (χ : mappingCone f ⟶ mappingCone θ)
    (hχ : χ = mappingCone.map f θ (𝟙 K) g (by rw [hθ, Category.id_comp])) :
    (complexConeCompHomotopyEquiv f g θ hθ χ hχ).hom ≫ (mappingCone.triangle χ).mor₃ =
      (mappingCone.triangle g).mor₃ ≫ (mappingCone.inr f)⟦(1 : ℤ)⟧' := by
  subst θ
  subst χ
  exact mappingConeCompHomotopyEquiv_comm₂ f g

end SerrePositivity.DifferentialGraded
