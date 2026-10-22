module
public import SerrePositivity.InfinityCategories.Derived.Gluing.JoinTensorLeftFactorNaturality

/-! join の第一因子に全パラメーターを残し、第二因子を固定する自然な比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
variable (A B K : SSet.{u})

def dgGluingJoinParameterComparison : join A B ⊗ K ⟶ join (A ⊗ K) B :=
  (β_ (join A B) K).hom ≫ joinTensorLeft K A B ≫ joinMap (β_ K A).hom (𝟙 B)

lemma dgGluingJoinParameterComparison_inl :
    (joinInl A B ▷ K) ≫ dgGluingJoinParameterComparison A B K = joinInl (A ⊗ K) B := by
  have hn : (joinInl A B ▷ K) ≫ (β_ (join A B) K).hom =
      (β_ A K).hom ≫ (K ◁ joinInl A B) := rfl
  have hl := joinTensorLeft_inl K A B
  rw [dgGluingJoinParameterComparison, ← Category.assoc, hn, Category.assoc,
    reassoc_of% hl, joinInl_joinMap, SymmetricCategory.symmetry_assoc]

lemma dgGluingJoinParameterComparison_inr :
    (joinInr A B ▷ K) ≫ dgGluingJoinParameterComparison A B K =
      fst B K ≫ joinInr (A ⊗ K) B := by
  have hn : (joinInr A B ▷ K) ≫ (β_ (join A B) K).hom =
      (β_ B K).hom ≫ (K ◁ joinInr A B) := rfl
  have hl := joinTensorLeft_inr K A B
  rw [dgGluingJoinParameterComparison, ← Category.assoc, hn, Category.assoc,
    reassoc_of% hl, joinInr_joinMap, Category.id_comp]
  rfl

lemma dgGluingJoinParameterComparison_left {A' : SSet.{u}} (f : A ⟶ A') :
    (joinMap f (𝟙 B) ▷ K) ≫ dgGluingJoinParameterComparison A' B K =
      dgGluingJoinParameterComparison A B K ≫ joinMap (f ▷ K) (𝟙 B) := by
  have hn : (joinMap f (𝟙 B) ▷ K) ≫ (β_ (join A' B) K).hom =
      (β_ (join A B) K).hom ≫ (K ◁ joinMap f (𝟙 B)) := rfl
  have hb : (K ◁ f) ≫ (β_ K A').hom = (β_ K A).hom ≫ (f ▷ K) := rfl
  have hl := dgGluingJoinTensorLeft_factor_naturality K B f
  rw [dgGluingJoinParameterComparison, ← Category.assoc, hn, Category.assoc,
    reassoc_of% hl, ← joinMap_comp,
    hb, Category.id_comp]
  have hj := joinMap_comp (β_ K A).hom (f ▷ K) (𝟙 B) (𝟙 B)
  simp only [Category.id_comp] at hj
  simpa only [dgGluingJoinParameterComparison, Category.assoc] using
    congrArg (fun k => (β_ (join A B) K).hom ≫ joinTensorLeft K A B ≫ k) hj

end SerrePositivity.InfinityCategories
