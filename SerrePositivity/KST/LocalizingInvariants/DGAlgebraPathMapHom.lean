module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathEndpoints
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexMappingCoconeMap

/-!
概要：代数射に沿う経路複体の実射と、両評価・比較 cochain の厳密な自然性。
方針：二直和上の差写像の可換性から、元の mapping cocone の射を使う。
規約：単位・積保存は後続。使われ方：実経路代数の関手性と相対経路。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
variable (R : Type u) [CommRing R] {A B : Mon (Complex R)} (f : A ⟶ B)

lemma difference_naturality : difference R A ≫ f.hom =
    biprod.map f.hom f.hom ≫ difference R B := by
  rw [difference_eq, difference_eq]
  simp only [Preadditive.sub_comp, Preadditive.comp_sub, biprod.map_fst, biprod.map_snd]

def mapHom : (algebra R A).X ⟶ (algebra R B).X :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap (difference R A) (difference R B)
    (biprod.map f.hom f.hom) f.hom (difference_naturality R f)

lemma mapHom_endpoints : mapHom R f ≫ endpointsHom R B =
    endpointsHom R A ≫ biprod.map f.hom f.hom :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst _ _ _ _ _

@[reassoc]
lemma mapHom_source : mapHom R f ≫ (source R B).hom = (source R A).hom ≫ f.hom := by
  change mapHom R f ≫ (endpointsHom R B ≫ biprod.fst) = _
  rw [← Category.assoc, mapHom_endpoints, Category.assoc, biprod.map_fst]
  rfl

@[reassoc]
lemma mapHom_target : mapHom R f ≫ (target R B).hom = (target R A).hom ≫ f.hom := by
  change mapHom R f ≫ (endpointsHom R B ≫ biprod.snd) = _
  rw [← Category.assoc, mapHom_endpoints, Category.assoc, biprod.map_snd]
  rfl

lemma mapHom_comparison :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison R _ _ (identityFunctor R B) (identityPoint R B)
      (identityPoint R B) (algebra R A).X (mapHom R f) =
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R _ _ (identityFunctor R A)
          (identityPoint R A) (identityPoint R A)).comp (Cochain.ofHom f.hom) (add_zero (-1)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_snd _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
