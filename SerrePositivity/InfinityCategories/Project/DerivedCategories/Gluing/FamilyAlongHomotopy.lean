module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IntervalUncurryHomotopy

/-! 同じホモトピーに沿う全パラメーター族は、両時刻と任意の単体面を厳密に保持する。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
variable {A B K E X : SSet.{u}} (V : A ⊗ E ⟶ X) {f g : K ⟶ E} (H : SSet.Homotopy f g)

def dgGluingFamilyAlongHomotopy : A ⊗ (K ⊗ (Δ[1] : SSet.{u})) ⟶ X :=
  (A ◁ H.h) ≫ V

lemma dgGluingFamilyAlongHomotopy_zero :
    (A ◁ (SSet.ι₀ : K ⟶ _)) ≫ dgGluingFamilyAlongHomotopy V H = (A ◁ f) ≫ V := by
  have hh := congrArg (fun k => (A ◁ k) ≫ V) H.h₀
  simpa only [dgGluingFamilyAlongHomotopy, whiskerLeft_comp, Category.assoc] using hh

lemma dgGluingFamilyAlongHomotopy_one :
    (A ◁ (SSet.ι₁ : K ⟶ _)) ≫ dgGluingFamilyAlongHomotopy V H = (A ◁ g) ≫ V := by
  have hh := congrArg (fun k => (A ◁ k) ≫ V) H.h₁
  simpa only [dgGluingFamilyAlongHomotopy, whiskerLeft_comp, Category.assoc] using hh

lemma dgGluingFamilyAlongHomotopy_face (t : B ⟶ A) :
    (t ▷ (K ⊗ (Δ[1] : SSet.{u}))) ≫ dgGluingFamilyAlongHomotopy V H =
      (B ◁ H.h) ≫ (t ▷ E) ≫ V := by
  rw [dgGluingFamilyAlongHomotopy, ← Category.assoc, ← whisker_exchange, Category.assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
