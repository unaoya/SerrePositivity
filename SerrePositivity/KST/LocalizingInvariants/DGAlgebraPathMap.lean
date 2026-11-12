module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathMapComparison
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathDiagonal

/-!
概要：代数射に沿う経路射の単位と積保存を証明し、実代数射に束ねる。
方針：元の両端と比較 cochain を保ったまま、comma Hom の三成分の一意性を使う。
規約：両端だけの一致で積保存を結論しない。使われ方：相対経路の代数的引き戻し。
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

lemma mapHom_one : η[(algebra R A).X] ≫ mapHom R f = η[(algebra R B).X] := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHom_ext R _ _ (identityFunctor R B)
    (identityPoint R B) (identityPoint R B)
  · change (η[(algebra R A).X] ≫ mapHom R f) ≫ (source R B).hom = _
    rw [Category.assoc, mapHom_source, ← Category.assoc,
      IsMonHom.one_hom, IsMonHom.one_hom]
    exact (IsMonHom.one_hom (source R B).hom).symm
  · change (η[(algebra R A).X] ≫ mapHom R f) ≫ (target R B).hom = _
    rw [Category.assoc, mapHom_target, ← Category.assoc,
      IsMonHom.one_hom, IsMonHom.one_hom]
    exact (IsMonHom.one_hom (target R B).hom).symm
  · have hu : (Cochain.ofHom η[(algebra R A).X]).comp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R _ _ (identityFunctor R A)
          (identityPoint R A) (identityPoint R A)) (zero_add (-1)) = 0 :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_comparison R _ _ _ _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison_precompose, mapHom_comparison,
      ← Cochain.comp_assoc_of_first_is_zero_cochain, hu, Cochain.zero_comp]
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_comparison R _ _ (identityFunctor R B)
      (identityPoint R B)).symm

lemma mapHom_mul : μ[(algebra R A).X] ≫ mapHom R f =
    (mapHom R f ⊗ₘ mapHom R f) ≫ μ[(algebra R B).X] := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHom_ext R _ _ (identityFunctor R B)
    (identityPoint R B) (identityPoint R B)
  · change (μ[(algebra R A).X] ≫ mapHom R f) ≫ (source R B).hom =
      ((mapHom R f ⊗ₘ mapHom R f) ≫ μ[(algebra R B).X]) ≫ (source R B).hom
    rw [Category.assoc, mapHom_source, ← Category.assoc, IsMonHom.mul_hom,
      Category.assoc, IsMonHom.mul_hom, ← Category.assoc, tensorHom_comp_tensorHom,
      ← mapHom_source, ← tensorHom_comp_tensorHom, Category.assoc]
    simpa only [Category.assoc] using
      (congrArg (fun h => (mapHom R f ⊗ₘ mapHom R f) ≫ h)
        (IsMonHom.mul_hom (source R B).hom)).symm
  · change (μ[(algebra R A).X] ≫ mapHom R f) ≫ (target R B).hom =
      ((mapHom R f ⊗ₘ mapHom R f) ≫ μ[(algebra R B).X]) ≫ (target R B).hom
    rw [Category.assoc, mapHom_target, ← Category.assoc, IsMonHom.mul_hom,
      Category.assoc, IsMonHom.mul_hom, ← Category.assoc, tensorHom_comp_tensorHom,
      ← mapHom_target, ← tensorHom_comp_tensorHom, Category.assoc]
    simpa only [Category.assoc] using
      (congrArg (fun h => (mapHom R f ⊗ₘ mapHom R f) ≫ h)
        (IsMonHom.mul_hom (target R B).hom)).symm
  · have hc (D : Mon (Complex R)) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison R _ _ (identityFunctor R D)
        (identityPoint R D) (identityPoint R D) ((algebra R D).X ⊗ (algebra R D).X)
        μ[(algebra R D).X] = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositePrimitive R _ _ (identityFunctor R D)
          (identityPoint R D) (identityPoint R D) (identityPoint R D) :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_comparison R _ _ _ _ _ _
    have hA : (Cochain.ofHom μ[(algebra R A).X]).comp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R _ _ (identityFunctor R A)
          (identityPoint R A) (identityPoint R A)) (zero_add (-1)) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositePrimitive R _ _ (identityFunctor R A)
          (identityPoint R A) (identityPoint R A) (identityPoint R A) := hc A
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison_precompose, mapHom_comparison,
      ← Cochain.comp_assoc_of_first_is_zero_cochain, hA,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison_precompose, hc, mapHom_product_comparison]

def map : algebra R A ⟶ algebra R B := Mon.Hom.mk' (mapHom R f)
  (mapHom_one R f) (mapHom_mul R f)

@[reassoc]
lemma map_source : map R f ≫ source R B = source R A ≫ f := by
  apply Mon.Hom.ext
  exact mapHom_source R f

@[reassoc]
lemma map_target : map R f ≫ target R B = target R A ≫ f := by
  apply Mon.Hom.ext
  exact mapHom_target R f

lemma map_quasiIso (hf : QuasiIso f.hom) : QuasiIso (map R f).hom := by
  have := source_quasiIso R B
  have : QuasiIso ((map R f).hom ≫ (source R B).hom) := by
    change QuasiIso ((map R f ≫ source R B).hom)
    rw [map_source]
    exact quasiIso_comp _ _ (hφ := source_quasiIso R A) (hφ' := hf)
  exact quasiIso_of_comp_right (map R f).hom (source R B).hom

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
