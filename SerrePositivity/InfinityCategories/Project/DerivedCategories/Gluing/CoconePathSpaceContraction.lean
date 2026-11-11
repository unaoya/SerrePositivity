module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CoconePathSpace
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexPinchedQuasiIso

/-! 同じ path 複体の実収縮を、零複体の空間模型へのホモトピー同値へ移す。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits HomologicalComplex CochainComplex DifferentialGraded
open scoped ZeroObject
variable {R : Type u} [CommRing R] (Q : Complex R)

def dgGluingCoconePathZeroHomotopyEquiv :
    HomotopyEquiv (mappingCocone (𝟙 Q)) (0 : Complex R) where
  hom := 0
  inv := 0
  homotopyHomInvId := by
    simpa only [zero_comp] using (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconePathContraction Q).symm
  homotopyInvHomId := Homotopy.ofEq (by simp)

lemma dgGluingCoconePathZero_quasiIso :
    QuasiIso (0 : mappingCocone (𝟙 Q) ⟶ (0 : Complex R)) :=
  (dgGluingCoconePathZeroHomotopyEquiv Q).quasiIso_hom

lemma dgGluingCoconePathSpace_zero_equivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (0 : mappingCocone (𝟙 Q) ⟶ (0 : Complex R))) := by
  let : QuasiIso (0 : mappingCocone (𝟙 Q) ⟶ (0 : Complex R)) :=
    dgGluingCoconePathZero_quasiIso Q
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_quasiIso_equivalence _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
