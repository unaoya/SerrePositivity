module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.JoinTensorLeftFactorNaturality

/-! join の第一因子に全パラメーターを残し、第二因子を固定する自然な比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
variable (A B K : SSet.{u})

def dgGluingJoinParameterComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (A ⊗ K) B :=
  (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) K).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft K A B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (β_ K A).hom (𝟙 B)

lemma dgGluingJoinParameterComparison_inl :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ▷ K) ≫ dgGluingJoinParameterComparison A B K = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (A ⊗ K) B := by
  have hn : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ▷ K) ≫ (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) K).hom =
      (β_ A K).hom ≫ (K ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B) := rfl
  have hl := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft_inl K A B
  rw [dgGluingJoinParameterComparison, ← Category.assoc, hn, Category.assoc,
    reassoc_of% hl, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, SymmetricCategory.symmetry_assoc]

lemma dgGluingJoinParameterComparison_inr :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ▷ K) ≫ dgGluingJoinParameterComparison A B K =
      fst B K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (A ⊗ K) B := by
  have hn : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ▷ K) ≫ (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) K).hom =
      (β_ B K).hom ≫ (K ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B) := rfl
  have hl := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft_inr K A B
  rw [dgGluingJoinParameterComparison, ← Category.assoc, hn, Category.assoc,
    reassoc_of% hl, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]
  rfl

lemma dgGluingJoinParameterComparison_left {A' : SSet.{u}} (f : A ⟶ A') :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 B) ▷ K) ≫ dgGluingJoinParameterComparison A' B K =
      dgGluingJoinParameterComparison A B K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (f ▷ K) (𝟙 B) := by
  have hn : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 B) ▷ K) ≫ (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A' B) K).hom =
      (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) K).hom ≫ (K ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 B)) := rfl
  have hb : (K ◁ f) ≫ (β_ K A').hom = (β_ K A).hom ≫ (f ▷ K) := rfl
  have hl := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingJoinTensorLeft_factor_naturality K B f
  rw [dgGluingJoinParameterComparison, ← Category.assoc, hn, Category.assoc,
    reassoc_of% hl, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp,
    hb, Category.id_comp]
  have hj := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp (β_ K A).hom (f ▷ K) (𝟙 B) (𝟙 B)
  simp only [Category.id_comp] at hj
  simpa only [dgGluingJoinParameterComparison, Category.assoc] using
    congrArg (fun k => (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) K).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft K A B ≫ k) hj

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
