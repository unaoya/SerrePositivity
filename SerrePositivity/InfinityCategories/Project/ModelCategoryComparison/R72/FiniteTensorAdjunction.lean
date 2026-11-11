module
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonsingular
public import Mathlib.AlgebraicTopology.SimplicialSet.Simplices
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Limits.Cones
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Tactic.CategoryTheory.Reassoc
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.NonsingularPresentation
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SubcomplexTensor
public import SerrePositivity.HomotopicalAlgebra.Simplicial.FiniteTensorAdjunction


/-!
分割で生成：docstring を書き直すこと
 # Reedy cofibrancy of standard simplices under a left Quillen functor

Finite nonsingular presentations are actual colimits of standard simplices.
A left adjoint preserves these presentations, identifying their constructed
finite tensor with its own value. Boundary inclusions then prove Reedy
cofibrancy, without a separate assumed latching condition.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72
variable {C : Type u} [Category.{v} C] [HasFiniteColimits C]
  (F : SSet.{v} ⥤ C) [F.IsLeftAdjoint]

variable (K : SSet.{v}) [K.Nonsingular] [K.Finite]

abbrev tensorCocone : Cocone (_root_.SerrePositivity.HomotopyFunctionComplex.NonsingularPresentation.diagram K ⋙ _root_.SerrePositivity.HomotopyFunctionComplex.StandardCosimplicial.diagram F) :=
  F.mapCocone (_root_.SerrePositivity.HomotopyFunctionComplex.NonsingularPresentation.cocone K)

def tensorCoconeIsColimit : IsColimit (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.tensorCocone F K) :=
  isColimitOfPreserves F (_root_.SerrePositivity.HomotopyFunctionComplex.NonsingularPresentation.isColimit K)

abbrev tensorIso : _root_.SerrePositivity.HomotopyFunctionComplex.FiniteTensor.obj (_root_.SerrePositivity.HomotopyFunctionComplex.StandardCosimplicial.diagram F) K ≅ F.obj K :=
  (colimit.isColimit _).coconePointUniqueUpToIso (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.tensorCoconeIsColimit F K)

@[reassoc]
lemma ι_tensorIso_hom (x : K.N) :
    colimit.ι (_root_.SerrePositivity.HomotopyFunctionComplex.NonsingularPresentation.diagram K ⋙ _root_.SerrePositivity.HomotopyFunctionComplex.StandardCosimplicial.diagram F) x ≫ (tensorIso F K).hom =
      F.map ((_root_.SerrePositivity.HomotopyFunctionComplex.NonsingularPresentation.cocone K).ι.app x) :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom (tensorCoconeIsColimit F K) x

lemma tensorIso_inclusion {n : SimplexCategory} (S : (SSet.stdSimplex.{v}.obj n).Subcomplex) :
    (tensorIso F S.toSSet).hom ≫ F.map S.ι = _root_.SerrePositivity.HomotopyFunctionComplex.SubcomplexTensor.inclusion S (_root_.SerrePositivity.HomotopyFunctionComplex.StandardCosimplicial.diagram F) := by
  apply colimit.hom_ext
  intro x
  have hi := ι_tensorIso_hom F S.toSSet x
  have hs : SSet.stdSimplex.map (_root_.SerrePositivity.HomotopyFunctionComplex.SubcomplexTensor.simplexMap S x) =
      (_root_.SerrePositivity.HomotopyFunctionComplex.NonsingularPresentation.cocone S.toSSet).ι.app x ≫ S.ι :=
    SSet.stdSimplex.fullyFaithful.map_preimage _
  have hd : colimit.ι (_root_.SerrePositivity.HomotopyFunctionComplex.SubcomplexTensor.diagram S ⋙ _root_.SerrePositivity.HomotopyFunctionComplex.StandardCosimplicial.diagram F) x ≫
      _root_.SerrePositivity.HomotopyFunctionComplex.SubcomplexTensor.inclusion S (_root_.SerrePositivity.HomotopyFunctionComplex.StandardCosimplicial.diagram F) = F.map (SSet.stdSimplex.map
        (_root_.SerrePositivity.HomotopyFunctionComplex.SubcomplexTensor.simplexMap S x)) := colimit.ι_desc _ _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f ↦ f ≫ F.map S.ι) hi).trans
      ((F.map_comp _ _).symm.trans ((congrArg F.map hs.symm).trans hd.symm)))

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72
