module
public import SerrePositivity.HomologicalAlgebra.FreeWeightEndEvaluation
public import SerrePositivity.HomologicalAlgebra.StandardSimplexWeight

/-!
概要：標準単体の自由線形重みからの end を、元の余単体複体へ戻す。
方針：各単体次数の自由 Yoneda 評価を使い、面と退化も同じ添字の射で照合する。
規約：二重反対圏は opOpEquivalence で明示して移す。元の図式の射を選び直さない。
使われ方：HA 1.2.4、G10 の標準単体の重み付き end と積 Tot の計算。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]

/-- 標準重みの基底へ、同じ余単体図式を二重反対圏の比較で移す。 -/
def doubleOppositeDiagram (X : CosimplicialObject (Complex A)) :
    SimplexCategoryᵒᵖᵒᵖ ⥤ Complex A := (opOpEquivalence SimplexCategory).functor ⋙ X

/-- 標準単体の全重みへの線形 end を取った余単体複体。 -/
def standardWeightEnd (X : CosimplicialObject (Complex A)) : CosimplicialObject (Complex A) :=
  (standardSimplexWeight (ModuleCat.of A A)).rightOp ⋙
    linearWeightEnd A (doubleOppositeDiagram X)

/-- 同じ自由生成元の評価によって、元の余単体図式へ戻る同型。 -/
def standardWeightEndIso (X : CosimplicialObject (Complex A)) : standardWeightEnd X ≅ X :=
  NatIso.ofComponents (fun n => (freeUnitWeightEndNatIso A (op n)).app (doubleOppositeDiagram X))
    (by
      intro n m f
      apply HomologicalComplex.Hom.ext
      funext q
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      have h := freePresheafHomLinearEquiv_precompose (R := A) (ModuleCat.of A A) f.op
        (doubleOppositeDiagram X ⋙ HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) q) z
      exact congrArg (fun g => g (1 : A)) h)

/-- 係数図式の全射も保持して、同じ標準重みの end を取る関手。 -/
def standardWeightEndFunctor :
    CosimplicialObject (Complex A) ⥤ CosimplicialObject (Complex A) :=
  (Functor.whiskeringLeft SimplexCategoryᵒᵖᵒᵖ SimplexCategory (Complex A)).obj
      (opOpEquivalence SimplexCategory).functor ⋙
    linearWeightEndFamily A ⋙
    (Functor.whiskeringLeft SimplexCategory (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A)ᵒᵖ
      (Complex A)).obj (standardSimplexWeight (ModuleCat.of A A)).rightOp

/-- 全関手族の各値は、同じ元の標準重みの end。 -/
theorem standardWeightEndFunctor_obj (X : CosimplicialObject (Complex A)) :
    standardWeightEndFunctor.obj X = standardWeightEnd X := rfl

/-- 自由重みの評価は係数図式を動かしても同じ余単体自然同型。 -/
def standardWeightEndNatIso : standardWeightEndFunctor (A := A) ≅ 𝟭 _ :=
  NatIso.ofComponents standardWeightEndIso (by
    intro X Y f
    apply NatTrans.ext
    funext n
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rfl)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
