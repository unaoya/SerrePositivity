module
public import SerrePositivity.HomologicalAlgebra.CochainProductTotalLinearComponents
public import SerrePositivity.HomologicalAlgebra.ExtendedChainHomRows
public import SerrePositivity.HomologicalAlgebra.WeightEndHomSigns
public import SerrePositivity.HomologicalAlgebra.LinearWeightEndTotalization

/-!
概要：鎖重みの積 end の各次数を、負次数へ延長した重みからの斉次射と同定する。
方針：積の指定成分を取り、縦横の微分に対応する符号を掛けて零延長へ戻す。
規約：内部次数は非有界。これは次数ごとの比較であり、微分との可換性とは区別する。
使われ方：HA 1.2.4、G10 の積全複体と Hom 複体の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.HomologicalAlgebra
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]
variable (K : ChainComplex (Jᵒᵖ ⥤ ModuleCat.{u} A) ℕ) (X : Jᵒᵖ ⥤ Complex A)

/-- Hom 微分に合わせる、各鎖次数の符号付き線形同値。 -/
def weightEndSignedRowsEquiv (q : ℤ) :
    (∀ n : ℕ, K.X n ⟶
      ((functorToComplexOfFunctors Jᵒᵖ (ModuleCat.{u} A) (.up ℤ)).obj X).X (q-n)) ≃ₗ[A]
    (∀ n : ℕ, K.X n ⟶
      ((functorToComplexOfFunctors Jᵒᵖ (ModuleCat.{u} A) (.up ℤ)).obj X).X (q-n)) where
  toFun f n := weightEndHomSign n q • f n
  invFun f n := weightEndHomSign n q • f n
  left_inv f := by funext n; simp only [smul_smul, weightEndHomSign_square, one_smul]
  right_inv f := by funext n; simp only [smul_smul, weightEndHomSign_square, one_smul]
  map_add' f g := by funext n; exact smul_add _ _ _
  map_smul' r f := by funext n; exact smul_comm (weightEndHomSign n q) r (f n)

/-- 積全複体の次数 q と、同じ重みからの次数 q の斉次射の線形同値。 -/
def weightEndHomComponentsEquiv (q : ℤ) :
    ((linearWeightEndTotalFunctor A X).obj (op K)).X q ≃ₗ[A]
      Cochain (K.extend ComplexShape.embeddingDownNat)
        ((functorToComplexOfFunctors Jᵒᵖ (ModuleCat.{u} A) (.up ℤ)).obj X) q :=
  (CochainProductTotal.componentsLinearEquiv
    ((linearWeightEndCochainFunctor A X).obj (op K)) q).trans
    ((weightEndSignedRowsEquiv A K X q).trans
      (extendedChainHomRowsLinearEquiv K
        ((functorToComplexOfFunctors Jᵒᵖ (ModuleCat.{u} A) (.up ℤ)).obj X) A q).symm)

end SerrePositivity.HomologicalAlgebra
