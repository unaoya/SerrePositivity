module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.NonsingularCoproduct
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-! # Finite tensors preserve finite coproducts

The actual coproduct of finite nonsingular simplicial sets remains in
the tensor domain. Its tensor and the tensor images of the injections
form a colimit cofan in C, using only finite colimits there.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.HomotopyFunctionComplex.FiniteTensor
variable {C : Type u} [Category.{v} C] [HasFiniteColimits C] (A : SimplexCategory ⥤ C)
  {ι : Type v} [Finite ι] (X : ι → SSet.{v}) [∀ i, (X i).Nonsingular] [∀ i, (X i).Finite]

abbrev coproductCofan : Cofan (fun i ↦ obj A (X i)) :=
  Cofan.mk (obj A (∐ X)) (fun i ↦ map A (Sigma.ι X i))

namespace Coproduct

def simplexDesc (s : Cofan (fun i ↦ obj A (X i))) : (∐ X) ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj s.pt :=
  Sigma.desc (fun i ↦ (homEquiv A (X i) s.pt).symm (s.inj i))

def desc (s : Cofan (fun i ↦ obj A (X i))) : obj A (∐ X) ⟶ s.pt :=
  homEquiv A (∐ X) s.pt (simplexDesc A X s)

lemma inj_desc (s : Cofan (fun i ↦ obj A (X i))) (i : ι) :
    map A (Sigma.ι X i) ≫ desc A X s = s.inj i :=
  (map_comp_homEquiv_apply A (Sigma.ι X i) _).trans
    ((congrArg (homEquiv A (X i) s.pt) (Sigma.ι_comp_desc _ _)).trans
      ((homEquiv A (X i) s.pt).apply_symm_apply _))

lemma uniq (s : Cofan (fun i ↦ obj A (X i))) (m : obj A (∐ X) ⟶ s.pt)
    (hm : ∀ i, map A (Sigma.ι X i) ≫ m = s.inj i) : m = desc A X s := by
  apply (homEquiv A (∐ X) s.pt).symm.injective
  apply Sigma.hom_ext
  intro i
  exact (homEquiv_symm_map_comp A (Sigma.ι X i) m).symm.trans
    ((congrArg (homEquiv A (X i) s.pt).symm ((hm i).trans (inj_desc A X s i).symm)).trans
      (homEquiv_symm_map_comp A (Sigma.ι X i) (desc A X s)))

end Coproduct

def isColimitCoproduct : IsColimit (coproductCofan A X) :=
  Cofan.IsColimit.mk _ (Coproduct.desc A X) (Coproduct.inj_desc A X) (Coproduct.uniq A X)

abbrev coproductIso : obj A (∐ X) ≅ ∐ (fun i ↦ obj A (X i)) :=
  (isColimitCoproduct A X).coconePointUniqueUpToIso (coproductIsCoproduct _)

@[reassoc (attr := simp)]
lemma ι_coproductIso_hom (i : ι) :
    map A (Sigma.ι X i) ≫ (coproductIso A X).hom = Sigma.ι (fun i ↦ obj A (X i)) i :=
  (isColimitCoproduct A X).comp_coconePointUniqueUpToIso_hom _ (Discrete.mk i)

lemma map_sigma_mem (Y : ι → SSet.{v}) [∀ i, (Y i).Nonsingular] [∀ i, (Y i).Finite]
    (f : ∀ i, X i ⟶ Y i) (W : MorphismProperty C)
    [W.IsStableUnderCoproductsOfShape ι] (hf : ∀ i, W (map A (f i))) :
    W (map A (Limits.Sigma.map f)) := by
  apply MorphismProperty.IsStableUnderColimitsOfShape.condition
    (W := W) (Discrete.functor (fun i ↦ obj A (X i)))
    (Discrete.functor (fun i ↦ obj A (Y i))) (coproductCofan A X) (coproductCofan A Y)
    (isColimitCoproduct A X) (isColimitCoproduct A Y)
    (Discrete.natTrans (fun i ↦ map A (f i.as))) (fun i ↦ hf i.as)
  intro i
  exact (map_comp A (Sigma.ι X i.as) (Limits.Sigma.map f)).trans
    ((congrArg (map A) (Sigma.ι_map f i.as)).trans (map_comp A (f i.as) (Sigma.ι Y i.as)).symm)

end SerrePositivity.HomotopyFunctionComplex.FiniteTensor
