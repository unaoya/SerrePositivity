module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMultiplicativeImageNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoLocalization

/-!
概要：実乗法的写像の連結成分から、元の代数の通常の擬同型局所化の Hom へ写す。
方針：元の準同型局所化関手と、その実反転性を全単体の像の構成に代入する。
規約：比較射の全単射性や導来写像空間の同値はここでは主張しない。
使われ方：導来比較の元の代数射での零次正規化。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory
open scoped Simplicial
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A B : Mon (Complex R))

def multiplicativeMappingPiZeroLocalization :
    SSet.π₀ (multiplicativeMappingSimplices R A B) →
      ((quasiIsoLocalization R).obj A ⟶ (quasiIsoLocalization R).obj B) :=
  multiplicativeMappingPiZeroImage R (quasiIsoLocalization R) (quasiIsoLocalization_inverts R)

lemma multiplicativeMappingPiZeroLocalization_original (f : A ⟶ B) :
    multiplicativeMappingPiZeroLocalization R A B
      (SSet.π₀.mk (multiplicativeMappingVertexEquiv R A B f)) = (quasiIsoLocalization R).map f :=
  multiplicativeMappingPiZeroImage_original R (quasiIsoLocalization R)
    (quasiIsoLocalization_inverts R) f

lemma multiplicativeMappingPiZeroLocalization_precompose {A' : Mon (Complex R)}
    (f : A' ⟶ A) (x : SSet.π₀ (multiplicativeMappingSimplices R A B)) :
    multiplicativeMappingPiZeroLocalization R A' B
      (SSet.mapπ₀ (multiplicativeMappingPrecompose R f B) x) =
        (quasiIsoLocalization R).map f ≫ multiplicativeMappingPiZeroLocalization R A B x :=
  multiplicativeMappingPiZeroImage_precompose R (quasiIsoLocalization R)
    (quasiIsoLocalization_inverts R) f x

lemma multiplicativeMappingPiZeroLocalization_postcompose {B' : Mon (Complex R)}
    (q : B ⟶ B') (x : SSet.π₀ (multiplicativeMappingSimplices R A B)) :
    multiplicativeMappingPiZeroLocalization R A B'
      (SSet.mapπ₀ (multiplicativeMappingPostcompose R A q) x) =
        multiplicativeMappingPiZeroLocalization R A B x ≫ (quasiIsoLocalization R).map q :=
  multiplicativeMappingPiZeroImage_postcompose R (quasiIsoLocalization R)
    (quasiIsoLocalization_inverts R) q x

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
