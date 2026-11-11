module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathModel
public import SerrePositivity.KST.LocalizingInvariants.CochainTensorPrecomposeZero

/-!
概要：経路代数への対角を、単位と積を保つ実代数射として構成する。
方針：両端を恒等射・比較 cochain を零として持ち上げ、comma Hom の一意性を使う。
規約：単なる複体の切断で代用しない。使われ方：経路模型と導来写像比較。
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
variable (R : Type u) [CommRing R] (B : Mon (Complex R))

lemma diagonal_boundary :
    δ (-1) 0 (0 : Cochain B.X B.X (-1)) +
      Cochain.ofHom (biprod.lift (𝟙 B.X) (𝟙 B.X) ≫ difference R B) = 0 := by
  rw [difference_eq]
  simp only [Preadditive.comp_sub, biprod.lift_fst, biprod.lift_snd, sub_self]
  simp

def diagonalHom : B.X ⟶ (algebra R B).X :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift R _ _ (identityFunctor R B) (identityPoint R B) (identityPoint R B)
    B.X (𝟙 _) (𝟙 _) 0 (diagonal_boundary R B)

lemma diagonalHom_source : diagonalHom R B ≫ (source R B).hom = 𝟙 B.X :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift_source R _ _ _ _ _ _ _ _ _ _

lemma diagonalHom_target : diagonalHom R B ≫ (target R B).hom = 𝟙 B.X :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift_replacement R _ _ _ _ _ _ _ _ _ _

lemma diagonalHom_comparison :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison R _ _ (identityFunctor R B) (identityPoint R B)
      (identityPoint R B) B.X (diagonalHom R B) = 0 := by
  apply Cochain.ext
  intro p q hpq
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison, Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  exact mappingCocone.lift_f_snd_v (difference R B)
    (biprod.lift (𝟙 B.X) (𝟙 B.X)) 0 (diagonal_boundary R B) p q hpq

lemma diagonalHom_one : η[B.X] ≫ diagonalHom R B = η[(algebra R B).X] := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHom_ext R _ _ (identityFunctor R B)
    (identityPoint R B) (identityPoint R B)
  · change (η[B.X] ≫ diagonalHom R B) ≫ (source R B).hom = _
    rw [Category.assoc, diagonalHom_source, Category.comp_id]
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_source R _ _ (identityFunctor R B) (identityPoint R B)).symm
  · change (η[B.X] ≫ diagonalHom R B) ≫ (target R B).hom = _
    rw [Category.assoc, diagonalHom_target, Category.comp_id]
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_replacement R _ _ (identityFunctor R B)
      (identityPoint R B)).symm
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison_precompose, diagonalHom_comparison, Cochain.comp_zero]
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_comparison R _ _ _ _).symm

lemma diagonal_tensor_comparison :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison R _ _ (identityFunctor R B) (identityPoint R B)
      (identityPoint R B) (B.X ⊗ B.X)
      ((diagonalHom R B ⊗ₘ diagonalHom R B) ≫ μ[(algebra R B).X]) = 0 := by
  let P := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R _ _ (identityFunctor R B)
    (identityPoint R B) (identityPoint R B)
  let i : B.X ⟶ P := diagonalHom R B
  have hz : (Cochain.ofHom i).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R _ _ (identityFunctor R B)
        (identityPoint R B) (identityPoint R B)) (zero_add (-1)) = 0 :=
    diagonalHom_comparison R B
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison R _ _ (identityFunctor R B) _ _ (B.X ⊗ B.X)
    ((i ⊗ₘ i) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition R _ _ _ _ _ _) = 0
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison_precompose, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_comparison,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositePrimitive, Cochain.comp_add,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositePrimitive, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositePrimitive,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    tensorRight_precompose_zero i i _ _ hz, Cochain.zero_comp, zero_add,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    tensorLeft_precompose_zero i i _ _ hz, Cochain.zero_comp]

lemma diagonalHom_mul : μ[B.X] ≫ diagonalHom R B =
    (diagonalHom R B ⊗ₘ diagonalHom R B) ≫ μ[(algebra R B).X] := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHom_ext R _ _ (identityFunctor R B)
    (identityPoint R B) (identityPoint R B)
  · change (μ[B.X] ≫ diagonalHom R B) ≫ (source R B).hom =
      ((diagonalHom R B ⊗ₘ diagonalHom R B) ≫ μ[(algebra R B).X]) ≫ (source R B).hom
    rw [Category.assoc, diagonalHom_source, Category.comp_id, Category.assoc,
      IsMonHom.mul_hom, ← Category.assoc, tensorHom_comp_tensorHom, diagonalHom_source,
      tensorHom_id, id_whiskerRight, Category.id_comp]
  · change (μ[B.X] ≫ diagonalHom R B) ≫ (target R B).hom =
      ((diagonalHom R B ⊗ₘ diagonalHom R B) ≫ μ[(algebra R B).X]) ≫ (target R B).hom
    rw [Category.assoc, diagonalHom_target, Category.comp_id, Category.assoc,
      IsMonHom.mul_hom, ← Category.assoc, tensorHom_comp_tensorHom, diagonalHom_target,
      tensorHom_id, id_whiskerRight, Category.id_comp]
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison_precompose, diagonalHom_comparison, Cochain.comp_zero,
      diagonal_tensor_comparison]

def diagonal : B ⟶ algebra R B := Mon.Hom.mk' (diagonalHom R B)
  (diagonalHom_one R B) (diagonalHom_mul R B)

lemma diagonal_source : diagonal R B ≫ source R B = 𝟙 B := by
  apply Mon.Hom.ext
  exact diagonalHom_source R B

lemma diagonal_target : diagonal R B ≫ target R B = 𝟙 B := by
  apply Mon.Hom.ext
  exact diagonalHom_target R B

lemma diagonal_quasiIso : QuasiIso (diagonal R B).hom := by
  have := source_quasiIso R B
  have : QuasiIso ((diagonal R B).hom ≫ (source R B).hom) := by
    change QuasiIso (diagonalHom R B ≫ (source R B).hom)
    rw [diagonalHom_source]
    infer_instance
  exact quasiIso_of_comp_right (diagonal R B).hom (source R B).hom

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
