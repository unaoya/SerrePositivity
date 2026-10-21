module
public import SerrePositivity.InfinityCategories.Derived.DGFunctorCommaAssociativityComparison
/-!
概要：実入力と比較対象分解を保持する対象に、実 mapping cocone Hom の dg 圏構造を与える。
方針：全二射影と比較 cochain の一意性から結合律を得て、実単位律とともに豊穣構造へ束ねる。
規約：全 Hom・全整数次数を保持。使われ方：任意の dg 加群値関手のcomma。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
/-- 同じ全三重 Hom からの、二つの実三重合成は厳密に一致する。 -/
theorem dgFunctorComma_assoc
    (W X Y Z : DGFunctorCommaObject R C E F) :
    dgFunctorCommaLeftAssociatedComposition R C E F W X Y Z =
      dgFunctorCommaRightAssociatedComposition R C E F W X Y Z := by
  apply dgFunctorCommaHom_ext R C E F W Z
  · exact dgFunctorComma_associativity_source R C E F W X Y Z
  · exact dgFunctorComma_associativity_replacement R C E F W X Y Z
  · exact dgFunctorComma_associativity_comparison R C E F W X Y Z
/-- 出力の射影性を仮定しない実分解対象と、同じ mapping cocone Hom の dg 圏。 -/
instance dgFunctorCommaDGCategory :
    DGCategory R (DGFunctorCommaObject R C E F) where
  Hom := dgFunctorCommaHomComplex R C E F
  id := dgFunctorCommaIdentity R C E F
  comp := dgFunctorCommaComposition R C E F
  id_comp X Y := by
    simpa only [dgFunctorCommaLeftUnitInsertion, Category.assoc] using
      dgFunctorComma_id_comp R C E F X Y
  comp_id X Y := by
    simpa only [dgFunctorCommaRightUnitInsertion, Category.assoc] using
      dgFunctorComma_comp_id R C E F X Y
  assoc W X Y Z := by
    have he := congrArg (fun f ↦
      (α_ (dgFunctorCommaHomComplex R C E F W X)
        (dgFunctorCommaHomComplex R C E F X Y)
        (dgFunctorCommaHomComplex R C E F Y Z)).inv ≫ f)
      (dgFunctorComma_assoc R C E F W X Y Z)
    simpa only [dgFunctorCommaLeftAssociatedComposition,
      dgFunctorCommaRightAssociatedComposition, Category.assoc,
      Iso.inv_hom_id_assoc] using he
end SerrePositivity.InfinityCategories
