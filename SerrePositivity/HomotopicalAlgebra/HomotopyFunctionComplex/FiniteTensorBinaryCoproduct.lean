module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensor
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryFan

/-! # Finite tensors preserve presented binary coproducts

The coproduct is supplied as an actual colimit in simplicial sets. All
three objects are finite and nonsingular; only finite colimits in C are used.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.HomotopyFunctionComplex.FiniteTensor
variable {C : Type u} [Category.{v} C] [HasFiniteColimits C] (A : SimplexCategory ⥤ C)
  {X Y Z : SSet.{v}} [X.Nonsingular] [X.Finite] [Y.Nonsingular] [Y.Finite]
  [Z.Nonsingular] [Z.Finite] {f : X ⟶ Z} {g : Y ⟶ Z}
  (h : IsColimit (BinaryCofan.mk f g))

namespace BinaryCoproduct

def simplexDesc (s : BinaryCofan (obj A X) (obj A Y)) : Z ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj s.pt :=
  BinaryCofan.IsColimit.desc h ((homEquiv A X s.pt).symm s.inl)
    ((homEquiv A Y s.pt).symm s.inr)

def desc (s : BinaryCofan (obj A X) (obj A Y)) : obj A Z ⟶ s.pt :=
  homEquiv A Z s.pt (simplexDesc A h s)

lemma inl_desc (s : BinaryCofan (obj A X) (obj A Y)) :
    map A f ≫ desc A h s = s.inl :=
  (map_comp_homEquiv_apply A f _).trans
    ((congrArg (homEquiv A X s.pt) (BinaryCofan.IsColimit.inl_desc h _ _)).trans
      ((homEquiv A X s.pt).apply_symm_apply _))

lemma inr_desc (s : BinaryCofan (obj A X) (obj A Y)) :
    map A g ≫ desc A h s = s.inr :=
  (map_comp_homEquiv_apply A g _).trans
    ((congrArg (homEquiv A Y s.pt) (BinaryCofan.IsColimit.inr_desc h _ _)).trans
      ((homEquiv A Y s.pt).apply_symm_apply _))

lemma uniq (s : BinaryCofan (obj A X) (obj A Y)) (m : obj A Z ⟶ s.pt)
    (hf : map A f ≫ m = s.inl) (hg : map A g ≫ m = s.inr) : m = desc A h s := by
  apply (homEquiv A Z s.pt).symm.injective
  apply BinaryCofan.IsColimit.hom_ext h
  · exact (homEquiv_symm_map_comp A f m).symm.trans
      ((congrArg (homEquiv A X s.pt).symm (hf.trans (inl_desc A h s).symm)).trans
        (homEquiv_symm_map_comp A f (desc A h s)))
  · exact (homEquiv_symm_map_comp A g m).symm.trans
      ((congrArg (homEquiv A Y s.pt).symm (hg.trans (inr_desc A h s).symm)).trans
        (homEquiv_symm_map_comp A g (desc A h s)))

end BinaryCoproduct

def isColimitBinaryCoproduct : IsColimit (BinaryCofan.mk (map A f) (map A g)) :=
  BinaryCofan.IsColimit.mk _ (fun p q ↦ BinaryCoproduct.desc A h (BinaryCofan.mk p q))
    (fun p q ↦ BinaryCoproduct.inl_desc A h (BinaryCofan.mk p q))
    (fun p q ↦ BinaryCoproduct.inr_desc A h (BinaryCofan.mk p q))
    (fun p q m hf hg ↦ BinaryCoproduct.uniq A h (BinaryCofan.mk p q) m hf hg)

end SerrePositivity.HomotopyFunctionComplex.FiniteTensor
