module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.EnrichedCochainUnit
/-! 閉射による後合成と比較 cochain の二項を、全整数次数で因子分解する。 -/
@[expose] public section
open CategoryTheory MonoidalCategory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
variable {R : Type u} [CommRing R] (E : Type v) [DGCategory R E]
lemma dgGluingCochain_rightClosed (X Y Z : E)
    (g : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
    {K P : Complex R} (i : 𝟙_ (Complex R) ⟶ K) (a : K ⟶ homObject R E Y Z)
    (hi : i ≫ a = ForgetEnrichment.homTo (Complex R) g)
    (p : ℤ) (h : Cochain P (homObject R E X Y) p) :
    (Cochain.ofHom ((ρ_ P).inv ≫ P ◁ i)).comp
      (((tensorRightHom K P (homObject R E X Y)).f p h).comp
        (Cochain.ofHom ((𝟙 _ ⊗ₘ a) ≫ eComp (Complex R) X Y Z)) (add_zero p))
      (zero_add p) = h.comp
        (Cochain.ofHom (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X) g))
        (add_zero p) := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexRightUnitInsertion_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp]
  congr 2
  simp only [Category.assoc]
  rw [whiskerLeft_comp_tensorHom_assoc, hi]
  rfl

lemma dgGluingCochain_insertion_natural {P Q K : Complex R} (a : P ⟶ Q) (i : 𝟙_ (Complex R) ⟶ K) :
    (ρ_ P).inv ≫ P ◁ i ≫ a ▷ K = a ≫ (ρ_ Q).inv ≫ Q ◁ i := by
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexRightUnitInsertion_cochain i 0 (Cochain.ofHom a)
  simp only [tensorRightHom_ofHom, ← Cochain.ofHom_comp] at he
  exact Cochain.ofHom_injective he

lemma dgGluingCochain_second_factor (X Y Z : E) {P K : Complex R}
    (a : P ⟶ homObject R E X Y) (i : 𝟙_ (Complex R) ⟶ K)
    (p : ℤ) (h : Cochain K (homObject R E Y Z) p) :
    (Cochain.ofHom ((ρ_ P).inv ≫ P ◁ i)).comp
      (((tensorLeftHom P K (homObject R E Y Z)).f p h).comp
        (Cochain.ofHom ((a ⊗ₘ 𝟙 _) ≫ eComp (Complex R) X Y Z)) (add_zero p))
      (zero_add p) =
    (Cochain.ofHom a).comp
      ((Cochain.ofHom ((ρ_ (homObject R E X Y)).inv ≫ (homObject R E X Y) ◁ i)).comp
        (((tensorLeftHom (homObject R E X Y) K (homObject R E Y Z)).f p h).comp
          (Cochain.ofHom (eComp (Complex R) X Y Z)) (add_zero p)) (zero_add p))
      (zero_add p) := by
  simp only [tensorHom_def', MonoidalCategory.whiskerLeft_id, Category.id_comp]
  rw [Cochain.ofHom_comp (a ▷ homObject R E Y Z) (eComp (Complex R) X Y Z),
    ← Cochain.comp_assoc_of_third_is_zero_cochain
      ((tensorLeftHom P K (homObject R E Y Z)).f p h),
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexLeftTensor_cochain_chain_naturality]
  simp only [Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain
      (Cochain.ofHom ((ρ_ P).inv ≫ P ◁ i)) (Cochain.ofHom (a ▷ K)),
    ← Cochain.ofHom_comp, Category.assoc, dgGluingCochain_insertion_natural]
  simp only [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
