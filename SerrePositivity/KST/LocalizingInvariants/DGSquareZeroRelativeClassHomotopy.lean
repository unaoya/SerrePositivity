module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeClassMap
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeTransportHomotopy

/-!
概要：同じ係数射の class 二重経路から、元の class 模型射を結ぶ実経路を構成する。
方針：実輸送間の経路を、元の係数模型射で前合成する。
規約：実模型と両射影を保持。使われ方：fixed 模型の右逆三角形の比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
variable {R : Type u} [CommRing R] {A W : Mon (Complex R)} {M N : Bimod A A}
  (m : M ⟶ N) (a : W ⟶ SquareZero.algebra A M) (b : W ⟶ SquareZero.algebra A N)
  {q : W ⟶ A} {v w : SquareZero.RelativeWitness q N
    (a ≫ SquareZero.coefficientMap A m) b} (h : SquareZero.RelativeWitnessSquare v w)

def classModelMapHomotopy : DGAlgebra.Path.Witness R
    (classModelMap m a b v) (classModelMap m a b w) :=
  (transportHomotopy N h).precomp
    (coefficientModelMap m a (a ≫ SquareZero.coefficientMap A m) rfl)

lemma classModelMapHomotopy_left : (classModelMapHomotopy m a b h).hom ≫
    DGAlgebra.Path.map R (relativeLeft N b) =
      relativeLeft M a ≫ DGAlgebra.Path.diagonal R W := by
  change (_ ≫ (transportHomotopy N h).hom) ≫ _ = _
  rw [Category.assoc, transportHomotopy_left, ← Category.assoc, coefficientModelMap_left]

lemma classModelMapHomotopy_right : (classModelMapHomotopy m a b h).hom ≫
    DGAlgebra.Path.map R (relativeRight N b) =
      relativeRight M a ≫ DGAlgebra.Path.diagonal R A := by
  change (_ ≫ (transportHomotopy N h).hom) ≫ _ = _
  rw [Category.assoc, transportHomotopy_right, ← Category.assoc, coefficientModelMap_right]

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
