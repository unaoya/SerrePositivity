module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TrivialFibrationHomotopy

/-! 自明 Kan fibration の同じ基底上で、全時刻の基底を固定する実ホモトピーを選ぶ。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

def dgGluingHomotopy_of_trivialFibration_post_eq {A E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] (f g : A ⟶ E) (h : f ≫ p = g ≫ p) :
    SSet.Homotopy f g :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_homotopy_over_trivialKanFibration p f g h)

lemma dgGluingHomotopy_of_trivialFibration_post_eq_over {A E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] (f g : A ⟶ E) (h : f ≫ p = g ≫ p) :
    (dgGluingHomotopy_of_trivialFibration_post_eq p f g h).h ≫ p =
      fst A (Δ[1] : SSet.{u}) ≫ g ≫ p :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_homotopy_over_trivialKanFibration p f g h)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
