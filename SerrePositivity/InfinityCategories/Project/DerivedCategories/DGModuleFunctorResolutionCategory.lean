module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionAssociativityComparison
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
/-- 同じ全三重 Hom からの、二つの実三重合成は厳密に一致する。 -/
theorem dgModuleFunctorResolution_assoc
    (W X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionLeftAssociatedComposition R C E F W X Y Z =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionRightAssociatedComposition R C E F W X Y Z := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHom_ext R C E F W Z
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolution_associativity_source R C E F W X Y Z
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolution_associativity_replacement R C E F W X Y Z
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolution_associativity_comparison R C E F W X Y Z
/-- 出力の射影性を仮定しない実分解対象と、同じ mapping cocone Hom の dg 圏。 -/
instance dgModuleFunctorResolutionDGCategory :
    DGCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) where
  Hom := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F
  id := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionIdentity R C E F
  comp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionComposition R C E F
  id_comp X Y := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionLeftUnitInsertion, Category.assoc] using
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolution_id_comp R C E F X Y
  comp_id X Y := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionRightUnitInsertion, Category.assoc] using
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolution_comp_id R C E F X Y
  assoc W X Y Z := by
    have he := congrArg (fun f ↦
      (α_ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F W X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F X Y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F Y Z)).inv ≫ f)
      (dgModuleFunctorResolution_assoc R C E F W X Y Z)
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionLeftAssociatedComposition,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionRightAssociatedComposition, Category.assoc,
      Iso.inv_hom_id_assoc] using he
end SerrePositivity.InfinityCategories.Project.DerivedCategories
