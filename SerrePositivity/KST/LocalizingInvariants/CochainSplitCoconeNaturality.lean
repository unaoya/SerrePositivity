module

public import SerrePositivity.KST.LocalizingInvariants.CochainSplitCoconeHomology
public import SerrePositivity.KST.LocalizingInvariants.CochainMappingCoconeMapQuasiIso

/-!
概要：零切断の負符号の cocone と係数の負一 shift の比較は、元の直和射に自然である。
方針：元の cone 商比較の自然性を shift し、元のホモロジー shift 同型へ移す。
規約：元の二つの成分と負符号を保持。使われ方：平方零拡大の層の射の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CochainComplex HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] {P T P' T' : Complex R} (a : P ⟶ P') (b : T ⟶ T')

def cochainNegInlCoconeMap : mappingCocone (-(biprod.inl : P ⟶ P ⊞ T)) ⟶
    mappingCocone (-(biprod.inl : P' ⟶ P' ⊞ T')) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap _ _ a (biprod.map a b) (by simp)

lemma cochainNegInlCoconeComparison_naturality : cochainNegInlCoconeMap a b ≫
    cochainNegInlCoconeComparison P' T' = cochainNegInlCoconeComparison P T ≫ b⟦(-1 : ℤ)⟧' := by
  have h := cochainConeQuotient_naturality (-(biprod.inl : P ⟶ P ⊞ T))
    (biprod.snd : P ⊞ T ⟶ T) (by simp) (-(biprod.inl : P' ⟶ P' ⊞ T'))
    (biprod.snd : P' ⊞ T' ⟶ T') (by simp) a (biprod.map a b) b (by simp) (by simp)
  rw [cochainNegInlCoconeMap, cochainMappingCoconeMap_eq_shift]
  exact (CategoryTheory.shiftFunctor (Complex R) (-1 : ℤ)).map_comp _ _ |>.symm.trans
    ((congrArg (fun t => t⟦(-1 : ℤ)⟧') h).trans
      ((CategoryTheory.shiftFunctor (Complex R) (-1 : ℤ)).map_comp _ _))

lemma cochainNegInlCoconeHomologyIso_naturality (j : ℤ) :
    homologyMap (cochainNegInlCoconeMap a b) j ≫ (cochainNegInlCoconeHomologyIso P' T' j).hom =
      (cochainNegInlCoconeHomologyIso P T j).hom ≫ homologyMap b (j - 1) := by
  let e := (homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftIso (-1) j (j - 1) (by omega)
  have he : homologyMap (b⟦(-1 : ℤ)⟧') j ≫ (e.app T').hom =
      (e.app T).hom ≫ homologyMap b (j - 1) := e.hom.naturality b
  change homologyMap (cochainNegInlCoconeMap a b) j ≫
    homologyMap (cochainNegInlCoconeComparison P' T') j ≫ (e.app T').hom =
      (homologyMap (cochainNegInlCoconeComparison P T) j ≫ (e.app T).hom) ≫ _
  rw [← Category.assoc, ← homologyMap_comp, cochainNegInlCoconeComparison_naturality,
    homologyMap_comp, Category.assoc, he, Category.assoc]

end SerrePositivity.KST.LocalizingInvariants
