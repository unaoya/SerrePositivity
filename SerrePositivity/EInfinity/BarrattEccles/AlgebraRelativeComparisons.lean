module

public import SerrePositivity.EInfinity.BarrattEccles.AlgebraRelativeCategory

/-!
# 元の包含・置換の両合成から恒等への指定自然変換

概要：実際の元の置換比較を同じ Hom の ULift へ移す。
方針：既存の比較自然変換を元の up・down で前後合成する。
規約：新しい置換対象や成分を選ばず、元の全代数射に自然である。
使われ方：元の cofibrant hammock 包含の弱同値性。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra
variable (A : Type u) [CommRing A]
def cofibrantDKComparison :
    (cofibrantToAlgebraDKRelative A).functor ⋙ (algebraToCofibrantDKRelative A).functor ⟶
      𝟭 (cofibrantAlgebraRelativeCategory A).category :=
  Functor.whiskerLeft (ULiftHom.down.{u, u + 1, u + 1} (C := CofibrantAlgebra A))
    (Functor.whiskerRight (cofibrantAlgebraRestrictedComparison A)
      (ULiftHom.up.{u, u + 1, u + 1} (C := CofibrantAlgebra A)))
def algebraDKComparison :
    (algebraToCofibrantDKRelative A).functor ⋙ (cofibrantToAlgebraDKRelative A).functor ⟶
      𝟭 (algebraRelativeCategory A).category :=
  Functor.whiskerLeft (ULiftHom.down.{u, u + 1, u + 1} (C := (operad A).Algebra))
    (Functor.whiskerRight (cofibrantAlgebraReplacementComparison A)
      (ULiftHom.up.{u, u + 1, u + 1} (C := (operad A).Algebra)))
lemma cofibrantDKComparison_weak (X : (cofibrantAlgebraRelativeCategory A).category) :
    (cofibrantAlgebraRelativeCategory A).weakEquivalences ((cofibrantDKComparison A).app X) :=
  cofibrantAlgebraRestrictedComparison_weakEquivalence A X
lemma algebraDKComparison_weak (X : (algebraRelativeCategory A).category) :
    (algebraRelativeCategory A).weakEquivalences ((algebraDKComparison A).app X) :=
  cofibrantAlgebraReplacementComparison_weakEquivalence A X
end SerrePositivity.EInfinity.BarrattEccles
