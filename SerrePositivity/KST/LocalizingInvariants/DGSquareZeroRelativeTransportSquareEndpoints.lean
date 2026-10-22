module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeTransportSquare

/-!
概要：輸送の二重経路の外側両端を、元の二つの輸送射の全経路に同定する。
方針：affine な全二重経路公式を評価し、既存の実輸送公式と比較する。
規約：ホモロジーの一致で代用しない。使われ方：輸送射間の実乗法的経路。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
variable {R : Type u} [CommRing R] {A W : Mon (Complex R)} (N : Bimod A A)
  {q : W ⟶ A} {a b : W ⟶ SquareZero.algebra A N}
  {v w : SquareZero.RelativeWitness q N a b} (h : SquareZero.RelativeWitnessSquare v w)

lemma transportSquarePath_post_linear {D : Mon (Complex R)}
    (m : DGAlgebra.Path.algebra R (DGAlgebra.Path.algebra R (SquareZero.algebra A N)) ⟶ D) :
    (transportSquarePath N h ≫ m).hom =
      (transportConstantPath N (relativeLeft N a ≫ b ≫
        DGAlgebra.Path.diagonal R (SquareZero.algebra A N)) ≫ m).hom -
      ((relativeLeft N a ≫ h.hom) ≫ m).hom +
      (transportConstantPath N (relativePath N a) ≫ m).hom := by
  rw [Mon.comp_hom', transportSquarePath_linear, add_comp, sub_comp]
  rfl

lemma transportSquarePath_source : transportSquarePath N h ≫
    DGAlgebra.Path.source R (DGAlgebra.Path.algebra R (SquareZero.algebra A N)) =
      transport N v ≫ relativePath N b := by
  apply Mon.Hom.ext
  rw [transportSquarePath_post_linear]
  simp only [transportConstantPath, Category.assoc, DGAlgebra.Path.diagonal_source,
    Category.comp_id, h.source_eq]
  exact (transport_path_linear N v).symm

lemma transportSquarePath_target : transportSquarePath N h ≫
    DGAlgebra.Path.target R (DGAlgebra.Path.algebra R (SquareZero.algebra A N)) =
      transport N w ≫ relativePath N b := by
  apply Mon.Hom.ext
  rw [transportSquarePath_post_linear]
  simp only [transportConstantPath, Category.assoc, DGAlgebra.Path.diagonal_target,
    Category.comp_id, h.target_eq]
  exact (transport_path_linear N w).symm

lemma transportConstantPath_inner_source
    (s : relativeModel N a ⟶ DGAlgebra.Path.algebra R (SquareZero.algebra A N)) :
    transportConstantPath N s ≫
      DGAlgebra.Path.map R (DGAlgebra.Path.source R (SquareZero.algebra A N)) =
    (s ≫ DGAlgebra.Path.source R (SquareZero.algebra A N)) ≫
      DGAlgebra.Path.diagonal R (SquareZero.algebra A N) := by
  rw [transportConstantPath, Category.assoc, DGAlgebra.Path.diagonal_naturality,
    ← Category.assoc]

lemma transportConstantPath_inner_target
    (s : relativeModel N a ⟶ DGAlgebra.Path.algebra R (SquareZero.algebra A N)) :
    transportConstantPath N s ≫
      DGAlgebra.Path.map R (DGAlgebra.Path.target R (SquareZero.algebra A N)) =
    (s ≫ DGAlgebra.Path.target R (SquareZero.algebra A N)) ≫
      DGAlgebra.Path.diagonal R (SquareZero.algebra A N) := by
  rw [transportConstantPath, Category.assoc, DGAlgebra.Path.diagonal_naturality,
    ← Category.assoc]

lemma transportSquarePath_source_trace : transportSquarePath N h ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.source R (SquareZero.algebra A N)) =
      (relativeLeft N a ≫ b) ≫ DGAlgebra.Path.diagonal R (SquareZero.algebra A N) := by
  apply Mon.Hom.ext
  rw [transportSquarePath_post_linear, transportConstantPath_inner_source,
    transportConstantPath_inner_source]
  rw [Category.assoc (relativeLeft N a), Category.assoc b, DGAlgebra.Path.diagonal_source,
    Category.comp_id]
  have hs : relativePath N a ≫ DGAlgebra.Path.source R (SquareZero.algebra A N) =
      relativeLeft N a ≫ a := (relativeWitness N a).source_eq
  rw [hs]
  simp only [Category.assoc, h.source_trace]
  abel

lemma transportSquarePath_target_trace : transportSquarePath N h ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.target R (SquareZero.algebra A N)) =
      (relativeRight N a ≫ SquareZero.zeroSection A N) ≫
        DGAlgebra.Path.diagonal R (SquareZero.algebra A N) := by
  apply Mon.Hom.ext
  rw [transportSquarePath_post_linear, transportConstantPath_inner_target,
    transportConstantPath_inner_target]
  rw [Category.assoc (relativeLeft N a), Category.assoc b, DGAlgebra.Path.diagonal_target,
    Category.comp_id]
  have ht : relativePath N a ≫ DGAlgebra.Path.target R (SquareZero.algebra A N) =
      relativeRight N a ≫ SquareZero.zeroSection A N := (relativeWitness N a).target_eq
  rw [ht]
  simp only [Category.assoc, h.target_trace]
  abel

lemma transportSquarePath_base_trace : transportSquarePath N h ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.map R (SquareZero.projection A N)) =
      ((relativeLeft N a ≫ DGAlgebra.Path.diagonal R W) ≫
        DGAlgebra.Path.map R (b ≫ SquareZero.projection A N)) ≫
        DGAlgebra.Path.map R (DGAlgebra.Path.diagonal R A) := by
  rw [transportSquarePath, SquareZero.affineDoublePathHom_projection,
    transportSquare_first_base N h]
  simp only [Category.assoc, h.projection_eq, DGAlgebra.Path.diagonal_naturality]
  rw [← Category.assoc b, v.target_projection]

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
