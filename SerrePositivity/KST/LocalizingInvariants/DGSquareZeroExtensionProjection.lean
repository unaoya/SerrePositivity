module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroExtensionHomology
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathQuasiIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathFunctor

/-!
概要：平方零 class の底射が準同型なら、実拡大の右射影の次数別準同型性を得る。
方針：実模型の経路を底へ後合成し、既存の左射影の計算と準同型な底射を合成する。
規約：係数の二次数の消滅を明示。使われ方：元の源 class による像拡大。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
variable {R : Type u} [CommRing R] {A W : Mon (Complex R)} (N : Bimod A A)
  (a : W ⟶ SquareZero.algebra A N)

abbrev right : model N a ⟶ A :=
  DGAlgebra.HomotopyPullbackModel.right R a (SquareZero.zeroSection A N)

def rightWitness : DGAlgebra.Path.Witness R
    (DGAlgebra.HomotopyPullbackModel.left R a (SquareZero.zeroSection A N) ≫
      (a ≫ SquareZero.projection A N)) (right N a) := by
  have w := (DGAlgebra.HomotopyPullbackModel.witness R a (SquareZero.zeroSection A N)).postcomp
    (SquareZero.projection A N)
  simpa only [right, Category.assoc, SquareZero.zeroSection_projection, Category.comp_id] using w

lemma right_quasiIsoAt (hb : QuasiIso (a ≫ SquareZero.projection A N).hom)
    (j : ℤ) (h₀ : CategoryTheory.Limits.IsZero (N.X.homology (j - 1)))
    (h₁ : CategoryTheory.Limits.IsZero (N.X.homology j)) : QuasiIsoAt (right N a).hom j := by
  have := projection_quasiIsoAt N a j h₀ h₁
  have := hb
  apply ((rightWitness N a).quasiIsoAt_iff j).mp
  change QuasiIsoAt ((DGAlgebra.HomotopyPullbackModel.left R a
    (SquareZero.zeroSection A N)).hom ≫ (a ≫ SquareZero.projection A N).hom) j
  infer_instance

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
