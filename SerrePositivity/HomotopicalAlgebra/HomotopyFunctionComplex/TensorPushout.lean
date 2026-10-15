module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.TensorFunctor
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

def simplexDesc (s : PushoutCocone (map A sq.le₁₂) (map A sq.le₁₃)) :
    S₄.toSSet ⟶ (cosimplicialHom A).obj s.pt :=
  sq.isPushout.desc ((homEquiv S₂ A s.pt).symm s.inl) ((homEquiv S₃ A s.pt).symm s.inr)
    ((homEquiv_symm_map_comp A sq.le₁₂ s.inl).symm.trans
      ((congrArg (homEquiv S₁ A s.pt).symm s.condition).trans
        (homEquiv_symm_map_comp A sq.le₁₃ s.inr)))

def desc (s : PushoutCocone (map A sq.le₁₂) (map A sq.le₁₃)) : obj S₄ A ⟶ s.pt :=
  homEquiv S₄ A s.pt (simplexDesc A sq s)

lemma inl_desc (s : PushoutCocone (map A sq.le₁₂) (map A sq.le₁₃)) :
    map A sq.le₂₄ ≫ desc A sq s = s.inl :=
  (map_comp_homEquiv_apply A sq.le₂₄ _).trans
    ((congrArg (homEquiv S₂ A s.pt) (sq.isPushout.inl_desc _ _ _)).trans
      ((homEquiv S₂ A s.pt).apply_symm_apply s.inl))

lemma inr_desc (s : PushoutCocone (map A sq.le₁₂) (map A sq.le₁₃)) :
    map A sq.le₃₄ ≫ desc A sq s = s.inr :=
  (map_comp_homEquiv_apply A sq.le₃₄ _).trans
    ((congrArg (homEquiv S₃ A s.pt) (sq.isPushout.inr_desc _ _ _)).trans
      ((homEquiv S₃ A s.pt).apply_symm_apply s.inr))

lemma uniq (s : PushoutCocone (map A sq.le₁₂) (map A sq.le₁₃)) (m : obj S₄ A ⟶ s.pt)
    (h₂ : map A sq.le₂₄ ≫ m = s.inl) (h₃ : map A sq.le₃₄ ≫ m = s.inr) :
    m = desc A sq s := by
  apply (homEquiv S₄ A s.pt).symm.injective
  apply sq.isPushout.hom_ext
  · exact (homEquiv_symm_map_comp A sq.le₂₄ m).symm.trans
      ((congrArg (homEquiv S₂ A s.pt).symm (h₂.trans (inl_desc A sq s).symm)).trans
        (homEquiv_symm_map_comp A sq.le₂₄ (desc A sq s)))
  · exact (homEquiv_symm_map_comp A sq.le₃₄ m).symm.trans
      ((congrArg (homEquiv S₃ A s.pt).symm (h₃.trans (inr_desc A sq s).symm)).trans
        (homEquiv_symm_map_comp A sq.le₃₄ (desc A sq s)))

end Gluing

lemma isPushout : IsPushout (map A sq.le₁₂) (map A sq.le₁₃)
    (map A sq.le₂₄) (map A sq.le₃₄) where
  w := (map_comp A sq.le₁₂ sq.le₂₄).trans (map_comp A sq.le₁₃ sq.le₃₄).symm
  isColimit' := ⟨PushoutCocone.IsColimit.mk _ (Gluing.desc A sq)
    (Gluing.inl_desc A sq) (Gluing.inr_desc A sq) (Gluing.uniq A sq)⟩

end SerrePositivity.HomotopyFunctionComplex.SubcomplexTensor
