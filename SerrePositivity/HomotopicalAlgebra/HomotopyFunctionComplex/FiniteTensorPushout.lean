module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensor
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! # Finite nonsingular tensors preserve actual pushout squares -/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.HomotopyFunctionComplex.FiniteTensor
variable {C : Type u} [Category.{v} C] [HasFiniteColimits C]
  (A : SimplexCategory ⥤ C) {X₁ X₂ X₃ X₄ : SSet.{v}}
  [X₁.Nonsingular] [X₁.Finite] [X₂.Nonsingular] [X₂.Finite]
  [X₃.Nonsingular] [X₃.Finite] [X₄.Nonsingular] [X₄.Finite]
  {f : X₁ ⟶ X₂} {g : X₁ ⟶ X₃} {inl : X₂ ⟶ X₄} {inr : X₃ ⟶ X₄}
  (sq : IsPushout f g inl inr)

namespace Gluing

def simplexDesc (s : PushoutCocone (map A f) (map A g)) :
    X₄ ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj s.pt :=
  sq.desc ((homEquiv A X₂ s.pt).symm s.inl) ((homEquiv A X₃ s.pt).symm s.inr)
    ((homEquiv_symm_map_comp A f s.inl).symm.trans
      ((congrArg (homEquiv A X₁ s.pt).symm s.condition).trans
        (homEquiv_symm_map_comp A g s.inr)))

def desc (s : PushoutCocone (map A f) (map A g)) : obj A X₄ ⟶ s.pt :=
  homEquiv A X₄ s.pt (simplexDesc A sq s)

lemma inl_desc (s : PushoutCocone (map A f) (map A g)) :
    map A inl ≫ desc A sq s = s.inl :=
  (map_comp_homEquiv_apply A inl _).trans
    ((congrArg (homEquiv A X₂ s.pt) (sq.inl_desc _ _ _)).trans
      ((homEquiv A X₂ s.pt).apply_symm_apply s.inl))

lemma inr_desc (s : PushoutCocone (map A f) (map A g)) :
    map A inr ≫ desc A sq s = s.inr :=
  (map_comp_homEquiv_apply A inr _).trans
    ((congrArg (homEquiv A X₃ s.pt) (sq.inr_desc _ _ _)).trans
      ((homEquiv A X₃ s.pt).apply_symm_apply s.inr))

lemma uniq (s : PushoutCocone (map A f) (map A g)) (m : obj A X₄ ⟶ s.pt)
    (h₂ : map A inl ≫ m = s.inl) (h₃ : map A inr ≫ m = s.inr) :
    m = desc A sq s := by
  apply (homEquiv A X₄ s.pt).symm.injective
  apply sq.hom_ext
  · exact (homEquiv_symm_map_comp A inl m).symm.trans
      ((congrArg (homEquiv A X₂ s.pt).symm (h₂.trans (inl_desc A sq s).symm)).trans
        (homEquiv_symm_map_comp A inl (desc A sq s)))
  · exact (homEquiv_symm_map_comp A inr m).symm.trans
      ((congrArg (homEquiv A X₃ s.pt).symm (h₃.trans (inr_desc A sq s).symm)).trans
        (homEquiv_symm_map_comp A inr (desc A sq s)))

end Gluing

include sq in
lemma isPushout : IsPushout (map A f) (map A g)
    (map A inl) (map A inr) where
  w := (map_comp A f inl).trans
    ((congrArg (map A) sq.w).trans (map_comp A g inr).symm)
  isColimit' := ⟨PushoutCocone.IsColimit.mk _ (Gluing.desc A sq)
    (Gluing.inl_desc A sq) (Gluing.inr_desc A sq) (Gluing.uniq A sq)⟩

end SerrePositivity.HomotopyFunctionComplex.FiniteTensor
