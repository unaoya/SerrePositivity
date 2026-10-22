module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomotopyIsoPrecomposition

/-! 二つの実ホモトピー逆を、同じ二成分の直積写像へ移す。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

def dgGluingProductHomotopy {A B C D : SSet.{u}} {f g : A ⟶ B} {f' g' : C ⟶ D}
    (H : SSet.Homotopy f g) (K : SSet.Homotopy f' g') :
    SSet.Homotopy (f ⊗ₘ f') (g ⊗ₘ g') where
  h := lift ((fst A C ▷ (Δ[1] : SSet.{u})) ≫ H.h)
    ((snd A C ▷ (Δ[1] : SSet.{u})) ≫ K.h)
  h₀ := by
    simp only [comp_lift, SSet.ι₀_comp_assoc, H.h₀, K.h₀]
    rfl
  h₁ := by
    simp only [comp_lift, SSet.ι₁_comp_assoc, H.h₁, K.h₁]
    rfl
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

lemma dgGluingProductMap_homotopyEquivalence {A B C D : SSet.{u}}
    {f : A ⟶ B} {g : C ⟶ D} (hf : IsSimplicialHomotopyEquivalence f)
    (hg : IsSimplicialHomotopyEquivalence g) :
    IsSimplicialHomotopyEquivalence (f ⊗ₘ g) := by
  obtain ⟨f', ⟨H⟩, ⟨K⟩⟩ := hf
  obtain ⟨g', ⟨H'⟩, ⟨K'⟩⟩ := hg
  refine ⟨f' ⊗ₘ g', ?_, ?_⟩
  · refine ⟨?_⟩
    simpa only [tensorHom_comp_tensorHom, tensorHom_id, id_whiskerRight] using
      dgGluingProductHomotopy H H'
  · refine ⟨?_⟩
    simpa only [tensorHom_comp_tensorHom, tensorHom_id, id_whiskerRight] using
      dgGluingProductHomotopy K K'

end SerrePositivity.InfinityCategories
