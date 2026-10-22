module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeTransportSquareEndpoints
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeHomotopyPullbackPathWitness

/-!
概要：端点と底を固定する class 二重経路から、元の輸送射間の実経路を構成する。
方針：輸送の affine 二重経路を、相対 homotopy pullback の経路へ持ち上げる。
規約：同じ相対模型間の二射を結ぶ。使われ方：実逆三角形の class coherence。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
variable {R : Type u} [CommRing R] {A W : Mon (Complex R)} (N : Bimod A A)
  {q : W ⟶ A} {a b : W ⟶ SquareZero.algebra A N}
  {v w : SquareZero.RelativeWitness q N a b} (h : SquareZero.RelativeWitnessSquare v w)

def transportHomotopyMap : relativeModel N a ⟶ DGAlgebra.Path.algebra R (relativeModel N b) :=
  DGAlgebra.RelativeHomotopyPullback.pathLift R (SquareZero.projection A N) b
    (SquareZero.zeroSection A N) (relativeLeft N a ≫ DGAlgebra.Path.diagonal R W)
    (relativeRight N a ≫ DGAlgebra.Path.diagonal R A) (transportSquarePath N h)
    (by simpa only [Category.assoc, DGAlgebra.Path.diagonal_naturality] using
      transportSquarePath_source_trace N h)
    (by simpa only [Category.assoc, DGAlgebra.Path.diagonal_naturality] using
      transportSquarePath_target_trace N h)
    (transportSquarePath_base_trace N h)

def transportHomotopy : DGAlgebra.Path.Witness R (transport N v) (transport N w) where
  hom := transportHomotopyMap N h
  source_eq := by
    unfold transportHomotopyMap
    apply DGAlgebra.RelativeHomotopyPullback.pathLift_source_eq
    · change (relativeLeft N a ≫ DGAlgebra.Path.diagonal R W) ≫
        DGAlgebra.Path.source R W = transport N v ≫ relativeLeft N b
      rw [Category.assoc, DGAlgebra.Path.diagonal_source, Category.comp_id, transport_left]
    · change (relativeRight N a ≫ DGAlgebra.Path.diagonal R A) ≫
        DGAlgebra.Path.source R A = transport N v ≫ relativeRight N b
      rw [Category.assoc, DGAlgebra.Path.diagonal_source, Category.comp_id, transport_right]
    · exact transportSquarePath_source N h
  target_eq := by
    unfold transportHomotopyMap
    apply DGAlgebra.RelativeHomotopyPullback.pathLift_target_eq
    · change (relativeLeft N a ≫ DGAlgebra.Path.diagonal R W) ≫
        DGAlgebra.Path.target R W = transport N w ≫ relativeLeft N b
      rw [Category.assoc, DGAlgebra.Path.diagonal_target, Category.comp_id, transport_left]
    · change (relativeRight N a ≫ DGAlgebra.Path.diagonal R A) ≫
        DGAlgebra.Path.target R A = transport N w ≫ relativeRight N b
      rw [Category.assoc, DGAlgebra.Path.diagonal_target, Category.comp_id, transport_right]
    · exact transportSquarePath_target N h

lemma transportHomotopy_left : (transportHomotopy N h).hom ≫
    DGAlgebra.Path.map R (relativeLeft N b) =
      relativeLeft N a ≫ DGAlgebra.Path.diagonal R W := by
  unfold transportHomotopy transportHomotopyMap
  apply DGAlgebra.RelativeHomotopyPullback.pathLift_left
  simpa only [Category.assoc, DGAlgebra.Path.diagonal_naturality] using
    transportSquarePath_target_trace N h

lemma transportHomotopy_right : (transportHomotopy N h).hom ≫
    DGAlgebra.Path.map R (relativeRight N b) =
      relativeRight N a ≫ DGAlgebra.Path.diagonal R A := by
  unfold transportHomotopy transportHomotopyMap
  apply DGAlgebra.RelativeHomotopyPullback.pathLift_right
  simpa only [Category.assoc, DGAlgebra.Path.diagonal_naturality] using
    transportSquarePath_target_trace N h

lemma transportHomotopy_path : (transportHomotopy N h).hom ≫
    DGAlgebra.Path.map R (relativePath N b) = transportSquarePath N h := by
  unfold transportHomotopy transportHomotopyMap
  apply DGAlgebra.RelativeHomotopyPullback.pathLift_path
  simpa only [Category.assoc, DGAlgebra.Path.diagonal_naturality] using
    transportSquarePath_target_trace N h

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
