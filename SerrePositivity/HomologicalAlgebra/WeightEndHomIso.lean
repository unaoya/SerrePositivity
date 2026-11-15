module
public import SerrePositivity.HomologicalAlgebra.WeightEndHomDifferential

/-!
概要：非有界の積 end と負次数へ延長した重みからの Hom 複体との指定同型。
方針：各次数の符号付き線形同値と微分の可換性を複体同型にまとめる。
規約：前向きの射は既存の成分同値そのもの。零鎖次数の評価を保つ。
使われ方：HA 1.2.4、G10 の BK 重みと Hom 空間の比較。
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

/-- 指定成分同値を前向きに持つ、積 end と線形 Hom の複体同型。 -/
def weightEndHomIso :
    (linearWeightEndTotalFunctor A X).obj (op K) ≅
      linearHomComplex A (K.extend ComplexShape.embeddingDownNat)
        ((functorToComplexOfFunctors Jᵒᵖ (ModuleCat.{u} A) (.up ℤ)).obj X) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => (weightEndHomComponentsEquiv A K X q).toModuleIso)
    (fun q r hqr => by
      have hr : q+1=r := hqr
      subst r
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact (weightEndHomComponentsEquiv_d A K X q z).symm)

/-- 前向きの射の成分は、指定した符号付き同値そのもの。 -/
theorem weightEndHomIso_hom_f (q : ℤ)
    (z : ((linearWeightEndTotalFunctor A X).obj (op K)).X q) :
    (weightEndHomIso A K X).hom.f q z = weightEndHomComponentsEquiv A K X q z := rfl

end SerrePositivity.HomologicalAlgebra
