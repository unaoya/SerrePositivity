module
public import SerrePositivity.HomologicalAlgebra.MapExtendComplex
public import SerrePositivity.HomologicalAlgebra.FunctorComplexExchangeEquivalence
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
概要：図式圏の零延長と対象ごとの零延長の、指定評価比較による全自然同型。
方針：既存 MapExtend の複体・加法関手の両自然性を評価関手に適用する。
規約：任意の複体形の埋め込みを許し、元の図式の全射を保持する。
使われ方：HA 1.2.4、G10 の対象ごとの smart 切断との比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex
namespace SerrePositivity.HomologicalAlgebra
variable (J : Type*) [Category* J] (C : Type*) [Category* C] [Abelian C]
variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')

/-- 零延長を対象ごとの複体評価と交換する全自然同型。 -/
def pointwiseExtendIso :
    e.extendFunctor (J ⥤ C) ⋙ complexOfFunctorsToFunctorToComplex ≅
      complexOfFunctorsToFunctorToComplex ⋙
        (Functor.whiskeringRight J (HomologicalComplex C c) (HomologicalComplex C c')).obj
          (e.extendFunctor C) :=
  NatIso.ofComponents
    (fun K => NatIso.ofComponents
      (fun j => mapExtendIso ((evaluation J C).obj j) e K)
      (fun f => SerrePositivity.mapExtendIso_natTrans ((evaluation J C).obj _) K e
        ((evaluation J C).map f)))
    (by
      intro K L f
      apply NatTrans.ext
      funext j
      exact SerrePositivity.mapExtendIso_naturality ((evaluation J C).obj j) e f)

end SerrePositivity.HomologicalAlgebra
