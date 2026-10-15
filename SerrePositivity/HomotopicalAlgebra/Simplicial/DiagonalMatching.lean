module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryHom
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalInternalHom
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.StandardCosimplicial
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-! # Matching objects of the concrete diagonal right adjoint

The actual latching colimit of standard simplices is the boundary simplex.
Contravariant internal Hom turns this colimit into the actual matching
limit. The comparison formula identifies restriction along the boundary.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.BisimplicialModel

/-- The actual latching object of standard simplices is the standard boundary. -/
def standardBoundaryIso (n : ℕ) :
    (latchingEvaluation simplex (SimplexCategory.mk n)).obj SSet.stdSimplex.{v} ≅
      (SSet.boundary.{v} n).toSSet :=
  (boundaryTensorIso SSet.stdSimplex.{v} n).symm ≪≫
    StandardCosimplicial.tensorIso (𝟭 SSet.{v}) (SSet.boundary n).toSSet

@[reassoc]
lemma standardBoundaryIso_fac (n : ℕ) :
    (standardBoundaryIso.{v} n).hom ≫ (SSet.boundary n).ι =
      (latchingComparison simplex (SimplexCategory.mk n)).app SSet.stdSimplex.{v} := by
  change (boundaryTensorIso SSet.stdSimplex.{v} n).inv ≫
      (StandardCosimplicial.tensorIso (𝟭 SSet.{v}) (SSet.boundary n).toSSet).hom ≫
        (𝟭 SSet.{v}).map (SSet.boundary n).ι = _
  rw [StandardCosimplicial.tensorIso_inclusion, boundaryTensorIso_comparison]
  exact Iso.inv_hom_id_assoc _ _

abbrev boundaryHom (Z : SSet.{v}) : SSet.{v}ᵒᵖ ⥤ SSet.{v} :=
  MonoidalClosed.internalHom.flip.obj Z

/-- An actual boundary internal Hom is the actual Reedy matching object. -/
def matchingBoundaryIso (Z : SSet.{v}) (n : ℕ) :
    (ihom (SSet.boundary.{v} n).toSSet).obj Z ≅
      (matchingEvaluation simplexOp (Opposite.op (SimplexCategory.mk n))).obj
        (internalHomRight.obj Z) :=
  (boundaryHom Z).mapIso (standardBoundaryIso n).op ≪≫
    BoundaryHom.iso simplex (SimplexCategory.mk n) SSet.stdSimplex.{v} (boundaryHom Z)

/-- The matching map is exactly restriction from the standard simplex to its boundary. -/
@[reassoc]
lemma matchingBoundaryIso_fac (Z : SSet.{v}) (n : ℕ) :
    (MonoidalClosed.internalHom.map (SSet.boundary.{v} n).ι.op).app Z ≫
      (matchingBoundaryIso Z n).hom =
        (matchingComparison simplexOp (Opposite.op (SimplexCategory.mk n))).app
          (internalHomRight.obj Z) := by
  change (boundaryHom Z).map (SSet.boundary n).ι.op ≫
      ((boundaryHom Z).map (standardBoundaryIso n).hom.op ≫
        (BoundaryHom.iso simplex (SimplexCategory.mk n) SSet.stdSimplex.{v}
          (boundaryHom Z)).hom) = _
  rw [← Category.assoc, ← (boundaryHom Z).map_comp, ← op_comp, standardBoundaryIso_fac]
  exact BoundaryHom.comparison simplex (SimplexCategory.mk n) SSet.stdSimplex.{v} (boundaryHom Z)

/-- Naturality of the actual boundary matching isomorphism in the target. -/
@[reassoc]
lemma matchingBoundaryIso_naturality {Z Z' : SSet.{v}} (p : Z ⟶ Z') (n : ℕ) :
    (matchingBoundaryIso Z n).hom ≫
        (matchingEvaluation simplexOp (Opposite.op (SimplexCategory.mk n))).map
          (internalHomRight.map p) =
      (ihom (SSet.boundary n).toSSet).map p ≫ (matchingBoundaryIso Z' n).hom := by
  let t := MonoidalClosed.internalHom.flip.map p
  let e := standardBoundaryIso.{v} n
  let i := BoundaryHom.iso simplex (SimplexCategory.mk n) SSet.stdSimplex.{v} (boundaryHom Z)
  let i' := BoundaryHom.iso simplex (SimplexCategory.mk n) SSet.stdSimplex.{v} (boundaryHom Z')
  have hnat := BoundaryHom.iso_naturality simplex (SimplexCategory.mk n)
    SSet.stdSimplex.{v} (boundaryHom Z) t
  have he := t.naturality e.hom.op
  change ((boundaryHom Z).map e.hom.op ≫ i.hom) ≫ _ =
    t.app (Opposite.op (SSet.boundary n).toSSet) ≫ ((boundaryHom Z').map e.hom.op ≫ i'.hom)
  rw [Category.assoc]
  refine (congrArg (fun k => (boundaryHom Z).map e.hom.op ≫ k) hnat).trans ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ i'.hom) he).trans (Category.assoc _ _ _))

end SerrePositivity.BisimplicialModel
