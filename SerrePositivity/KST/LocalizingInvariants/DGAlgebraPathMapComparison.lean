module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathMapHom
public import SerrePositivity.KST.LocalizingInvariants.CochainAlgebraProductNaturality

/-!
概要：経路複体の射は、実積の二つの比較 cochain を保つ。
方針：元の両評価と比較 cochain の自然性を、左右の積自然性へ渡す。
規約：全パラメータ tensor を保持する。使われ方：実経路代数射の積保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CochainComplex HomComplex
open scoped MonObj
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
variable (R : Type u) [CommRing R] {A B : Mon (Complex R)} (f : A ⟶ B)

lemma mapHom_product_comparison :
    (Cochain.ofHom (mapHom R f ⊗ₘ mapHom R f)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositePrimitive R _ _ (identityFunctor R B)
        (identityPoint R B) (identityPoint R B) (identityPoint R B)) (zero_add (-1)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositePrimitive R _ _ (identityFunctor R A)
        (identityPoint R A) (identityPoint R A) (identityPoint R A)).comp
          (Cochain.ofHom f.hom) (add_zero (-1)) := by
  let P := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R _ _ (identityFunctor R A)
    (identityPoint R A) (identityPoint R A)
  let Q := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R _ _ (identityFunctor R B)
    (identityPoint R B) (identityPoint R B)
  let k : P ⟶ Q := mapHom R f
  let sA : P ⟶ A.X := (source R A).hom
  let sB : Q ⟶ B.X := (source R B).hom
  let tA : P ⟶ A.X := (target R A).hom
  let tB : Q ⟶ B.X := (target R B).hom
  let hA : Cochain P A.X (-1) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R _ _ (identityFunctor R A)
    (identityPoint R A) (identityPoint R A)
  let hB : Cochain Q B.X (-1) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R _ _ (identityFunctor R B)
    (identityPoint R B) (identityPoint R B)
  have hs : k ≫ sB = sA ≫ f.hom := mapHom_source R f
  have ht : k ≫ tB = tA ≫ f.hom := mapHom_target R f
  have hh : (Cochain.ofHom k).comp hB (zero_add (-1)) =
      hA.comp (Cochain.ofHom f.hom) (add_zero (-1)) := mapHom_comparison R f
  have hr := cochainRightProduct_natural f k sA sB hs (-1) hA hB hh
  have hl := cochainLeftProduct_natural f k tA tB ht (-1) hA hB hh
  have he := congrArg₂ (fun a b => a + b) hr hl
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositePrimitive, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositePrimitive,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositePrimitive, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositionMap,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositionMap, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap,
    identityFunctor, EnrichedFunctor.id_map, Category.comp_id,
    Cochain.comp_add, Cochain.add_comp]
  exact he

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
