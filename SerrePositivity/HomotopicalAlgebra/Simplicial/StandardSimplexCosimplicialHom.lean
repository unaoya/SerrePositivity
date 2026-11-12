module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Hom.Basic
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.ResolutionHom

/-! # Standard cosimplicial frames under a left Quillen left adjoint

The source and target Hom universes are independent. The augmentation is
the actual collapse to the zero-simplex followed by the terminal-unit iso.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.HomotopyFunctionComplex.QuillenStandardFrame

abbrev zeroUnitIso : SSet.stdSimplex.{w}.obj (SimplexCategory.mk 0) ≅ (𝟙_ SSet.{w}) :=
  SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit

abbrev collapse (n : SimplexCategory) : n ⟶ SimplexCategory.mk 0 :=
  SimplexCategory.const n (SimplexCategory.mk 0) 0

def augmentation : SSet.stdSimplex.{w} ⟶ (Functor.const SimplexCategory).obj (𝟙_ SSet.{w}) where
  app n := SSet.stdSimplex.map (collapse n) ≫ zeroUnitIso.hom
  naturality n m f := by
    have hc : f ≫ collapse m = collapse n := by ext i; rfl
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
      ← Category.assoc, ← Functor.map_comp, hc]

/-- The actual cosimplicial Hom of standard simplices is the simplicial set itself. -/
def homIso : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom SSet.stdSimplex.{w} ≅ 𝟭 SSet.{w} :=
  NatIso.ofComponents (fun Y => NatIso.ofComponents (fun n =>
    Equiv.toIso (SSet.yonedaEquiv (X := Y) (n := n.unop))) (by
      intro n m f
      ext a
      exact (SSet.yonedaEquiv_naturality f.unop a).symm)) (by
    intro Y Z f
    ext n a
    exact SSet.yonedaEquiv_comp a f)

end SerrePositivity.HomotopyFunctionComplex.QuillenStandardFrame
