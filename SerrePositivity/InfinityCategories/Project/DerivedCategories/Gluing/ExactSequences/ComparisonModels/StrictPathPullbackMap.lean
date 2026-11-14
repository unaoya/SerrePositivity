module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ArrowEndpointPair
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath

/-! 厳密な同じ対角の引き戻しを、定値対角 path による引き戻し比較へ送る。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

def dgGluingConstantIntervalPath (Q : SSet.{u}) : Q ⟶ (ihom (Δ[1] : SSet.{u})).obj Q :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Q

lemma dgGluingConstantIntervalPath_endpoint (Q : SSet.{u}) (j : Fin 2) :
    dgGluingConstantIntervalPath Q ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm j) = 𝟙 Q := by
  rw [dgGluingConstantIntervalPath, Category.assoc]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl_endpoint Q j

variable {A B Q : SSet.{u}} (f : A ⟶ Q) (g : B ⟶ Q)

def dgGluingStrictPathPullbackMap :
    pullback f g ⟶ pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair Q) (f ⊗ₘ g) :=
  pullback.lift (pullback.fst f g ≫ f ≫ dgGluingConstantIntervalPath Q)
    (lift (pullback.fst f g) (pullback.snd f g)) (by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair, lift_fst, tensorHom_fst,
          lift_fst_assoc, dgGluingConstantIntervalPath_endpoint, Category.comp_id]
      · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair, lift_snd, tensorHom_snd,
          lift_snd_assoc, dgGluingConstantIntervalPath_endpoint, Category.comp_id]
        exact pullback.condition)

lemma dgGluingStrictPathPullbackMap_path :
    dgGluingStrictPathPullbackMap f g ≫ pullback.fst _ _ =
      pullback.fst f g ≫ f ≫ dgGluingConstantIntervalPath Q :=
  pullback.lift_fst _ _ _

lemma dgGluingStrictPathPullbackMap_inputs :
    dgGluingStrictPathPullbackMap f g ≫ pullback.snd _ _ =
      lift (pullback.fst f g) (pullback.snd f g) :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
