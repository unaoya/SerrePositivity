module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitness

/-!
概要：同じ底と両端を固定して、二つの実 class 経路を比較する二重経路。
方針：元の経路間の乗法的経路と、内部両端・底への全射影の式を保持する。
規約：二重経路の存在は定義だけから結論しない。使われ方：実模型輸送の経路比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] {A W : Mon (Complex R)} {N : Bimod A A}
  {q : W ⟶ A} {a b : W ⟶ algebra A N}

structure RelativeWitnessSquare (v w : RelativeWitness q N a b)
    extends DGAlgebra.Path.Witness R v.hom w.hom where
  source_trace : hom ≫ DGAlgebra.Path.map R (DGAlgebra.Path.source R (algebra A N)) =
    a ≫ DGAlgebra.Path.diagonal R (algebra A N)
  target_trace : hom ≫ DGAlgebra.Path.map R (DGAlgebra.Path.target R (algebra A N)) =
    b ≫ DGAlgebra.Path.diagonal R (algebra A N)
  projection_eq : hom ≫ DGAlgebra.Path.map R (DGAlgebra.Path.map R (projection A N)) =
    (q ≫ DGAlgebra.Path.diagonal R A) ≫ DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R A)

end SerrePositivity.KST.LocalizingInvariants.SquareZero
