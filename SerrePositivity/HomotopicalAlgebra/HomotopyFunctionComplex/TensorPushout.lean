module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.TensorFunctor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensorPushout
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-! # Finite subcomplex tensors preserve intersection/union pushouts -/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.HomotopyFunctionComplex.SubcomplexTensor
variable {n : SimplexCategory} {C : Type u} [Category.{v} C] [HasFiniteColimits C]
  (A : SimplexCategory ⥤ C) {S₁ S₂ S₃ S₄ : (SSet.stdSimplex.{v}.obj n).Subcomplex}
  (sq : SSet.Subcomplex.BicartSq S₁ S₂ S₃ S₄)

namespace Gluing

abbrev simplexDesc (s : PushoutCocone (map A sq.le₁₂) (map A sq.le₁₃)) :
    S₄.toSSet ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj s.pt :=
  FiniteTensor.Gluing.simplexDesc A sq.isPushout s

abbrev desc (s : PushoutCocone (map A sq.le₁₂) (map A sq.le₁₃)) : obj S₄ A ⟶ s.pt :=
  FiniteTensor.Gluing.desc A sq.isPushout s

lemma inl_desc (s : PushoutCocone (map A sq.le₁₂) (map A sq.le₁₃)) :
    map A sq.le₂₄ ≫ desc A sq s = s.inl :=
  FiniteTensor.Gluing.inl_desc A sq.isPushout s

lemma inr_desc (s : PushoutCocone (map A sq.le₁₂) (map A sq.le₁₃)) :
    map A sq.le₃₄ ≫ desc A sq s = s.inr :=
  FiniteTensor.Gluing.inr_desc A sq.isPushout s

lemma uniq (s : PushoutCocone (map A sq.le₁₂) (map A sq.le₁₃)) (m : obj S₄ A ⟶ s.pt)
    (h₂ : map A sq.le₂₄ ≫ m = s.inl) (h₃ : map A sq.le₃₄ ≫ m = s.inr) :
    m = desc A sq s := FiniteTensor.Gluing.uniq A sq.isPushout s m h₂ h₃

end Gluing

lemma isPushout : IsPushout (map A sq.le₁₂) (map A sq.le₁₃)
    (map A sq.le₂₄) (map A sq.le₃₄) := FiniteTensor.isPushout A sq.isPushout

end SerrePositivity.HomotopyFunctionComplex.SubcomplexTensor
