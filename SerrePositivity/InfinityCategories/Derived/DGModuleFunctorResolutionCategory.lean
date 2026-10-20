module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionAssociativityComparison
/-!
概要：実入力と半自由出力分解を保持する対象に、実 mapping cocone Hom の dg 圏構造を与える。
方針：全二射影と比較 cochain の一意性から結合律を得て、実単位律とともに豊穣構造へ束ねる。
規約：全 Hom・全整数次数を保持。使われ方：任意の dg 加群値関手の出力分解。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
/-- 同じ全三重 Hom からの、二つの実三重合成は厳密に一致する。 -/
theorem dgModuleFunctorResolution_assoc
    (W X Y Z : DGModuleFunctorResolutionObject R C E F) :
    dgModuleFunctorResolutionLeftAssociatedComposition R C E F W X Y Z =
      dgModuleFunctorResolutionRightAssociatedComposition R C E F W X Y Z := by
  apply dgModuleFunctorResolutionHom_ext R C E F W Z
  · exact dgModuleFunctorResolution_associativity_source R C E F W X Y Z
  · exact dgModuleFunctorResolution_associativity_replacement R C E F W X Y Z
  · exact dgModuleFunctorResolution_associativity_comparison R C E F W X Y Z
/-- 出力の射影性を仮定しない実分解対象と、同じ mapping cocone Hom の dg 圏。 -/
instance dgModuleFunctorResolutionDGCategory :
    DGCategory R (DGModuleFunctorResolutionObject R C E F) where
  Hom := dgModuleFunctorResolutionHomComplex R C E F
  id := dgModuleFunctorResolutionIdentity R C E F
  comp := dgModuleFunctorResolutionComposition R C E F
  id_comp X Y := by
    simpa only [dgModuleFunctorResolutionLeftUnitInsertion, Category.assoc] using
      dgModuleFunctorResolution_id_comp R C E F X Y
  comp_id X Y := by
    simpa only [dgModuleFunctorResolutionRightUnitInsertion, Category.assoc] using
      dgModuleFunctorResolution_comp_id R C E F X Y
  assoc W X Y Z := by
    have he := congrArg (fun f ↦
      (α_ (dgModuleFunctorResolutionHomComplex R C E F W X)
        (dgModuleFunctorResolutionHomComplex R C E F X Y)
        (dgModuleFunctorResolutionHomComplex R C E F Y Z)).inv ≫ f)
      (dgModuleFunctorResolution_assoc R C E F W X Y Z)
    simpa only [dgModuleFunctorResolutionLeftAssociatedComposition,
      dgModuleFunctorResolutionRightAssociatedComposition, Category.assoc,
      Iso.inv_hom_id_assoc] using he
end SerrePositivity.InfinityCategories
