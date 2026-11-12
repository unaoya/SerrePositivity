module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathMapLaws
public import SerrePositivity.KST.LocalizingInvariants.CochainTensorPrecompose

/-!
概要：経路代数の単位・積の比較 cochain を、元の両評価で表示する。
方針：comma dg 圏の実合成の二比較成分を同じ代数の乗法へ戻す。
規約：全複体上の等式。使われ方：connection の乗法保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CochainComplex HomComplex
open scoped MonObj
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
variable (R : Type u) [CommRing R] (B : Mon (Complex R))

lemma one_primitive : (Cochain.ofHom η[(algebra R B).X]).comp
    (primitive R B) (zero_add (-1)) = 0 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_comparison R _ _ _ _

lemma mul_primitive : (Cochain.ofHom μ[(algebra R B).X]).comp
    (primitive R B) (zero_add (-1)) =
      ((tensorRightHom (algebra R B).X (algebra R B).X B.X).f (-1)
        (primitive R B)).comp
        (Cochain.ofHom ((𝟙 B.X ⊗ₘ (source R B).hom) ≫ μ[B.X])) (add_zero (-1)) +
      ((tensorLeftHom (algebra R B).X (algebra R B).X B.X).f (-1)
        (primitive R B)).comp
        (Cochain.ofHom (((target R B).hom ⊗ₘ 𝟙 B.X) ≫ μ[B.X])) (add_zero (-1)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_comparison R _ _ (identityFunctor R B)
    (identityPoint R B) (identityPoint R B) (identityPoint R B)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositePrimitive,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositePrimitive, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositePrimitive,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositionMap, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositionMap,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap, identityFunctor, EnrichedFunctor.id_map,
    Category.comp_id] using! h

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
