module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGFunctors.DGFunctorCommaComparisonNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.EnrichedCochainUnit
/-!
概要：commaの実合成へ単位を挿入したとき、同じ全比較 cochain を回収する。
方針：二項の一方を零化し、もう一方を実豊穣単位律で回収する。
規約：全 Hom 複体上の等式。使われ方：comma dg 圏の左右単位律。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
/-- 元の dg 関手への実像も、同じ単位を保つ。 -/
lemma dgFunctorCommaIdentity_image :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity R C E F X ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R C E F X X =
        eId (Complex R) (F.obj X.source) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_source, F.map_id]
/-- 実左単位を全 Hom tensor の第一因子へ挿入する。 -/
def dgFunctorCommaLeftUnitInsertion :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X X ⊗
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y :=
  (λ_ _).inv ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity R C E F X ▷ _
/-- 実右単位を全 Hom tensor の第二因子へ挿入する。 -/
def dgFunctorCommaRightUnitInsertion :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y ⊗
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Y :=
  (ρ_ _).inv ≫ _ ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity R C E F Y
/-- 左単位では、第一比較項は零となる。 -/
lemma dgFunctorCommaLeftUnit_firstPrimitive :
    (Cochain.ofHom (dgFunctorCommaLeftUnitInsertion R C E F X Y)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositePrimitive R C E F X X Y) (zero_add (-1)) =
        0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositePrimitive,
    ← Cochain.comp_assoc_of_first_is_zero_cochain]
  have hz : (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity R C E F X)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X X) (zero_add (-1)) = 0 :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_comparison R C E F X
  rw [dgFunctorCommaLeftUnitInsertion,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexLeftUnitInsertion_rightTensor_zero _ _ _ hz, Cochain.zero_comp]
/-- 左単位では、第二比較項が元の同じ比較 cochain を回収する。 -/
lemma dgFunctorCommaLeftUnit_secondPrimitive :
    (Cochain.ofHom (dgFunctorCommaLeftUnitInsertion R C E F X Y)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositePrimitive R C E F X X Y) (zero_add (-1)) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedCochain_leftUnit E X.replacement (F.obj Y.source)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity R C E F X)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X X)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_replacement R C E F X) (-1)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y)
/-- 右単位では、第一比較項が元の同じ比較 cochain を回収する。 -/
lemma dgFunctorCommaRightUnit_firstPrimitive :
    (Cochain.ofHom (dgFunctorCommaRightUnitInsertion R C E F X Y)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositePrimitive R C E F X Y Y) (zero_add (-1)) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedCochain_rightUnit E X.replacement (F.obj Y.source)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity R C E F Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R C E F Y Y)
    (dgFunctorCommaIdentity_image R C E F Y) (-1)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y)
/-- 右単位では、第二比較項は零となる。 -/
lemma dgFunctorCommaRightUnit_secondPrimitive :
    (Cochain.ofHom (dgFunctorCommaRightUnitInsertion R C E F X Y)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositePrimitive R C E F X Y Y) (zero_add (-1)) =
        0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositePrimitive,
    ← Cochain.comp_assoc_of_first_is_zero_cochain]
  have hz : (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity R C E F Y)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F Y Y) (zero_add (-1)) = 0 :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_comparison R C E F Y
  rw [dgFunctorCommaRightUnitInsertion,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexRightUnitInsertion_leftTensor_zero _ _ _ hz, Cochain.zero_comp]
/-- 左単位と実合成の比較 cochain は、元の同じ比較 cochain。 -/
lemma dgFunctorCommaLeftUnit_comparison :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison R C E F X Y _
      (dgFunctorCommaLeftUnitInsertion R C E F X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition R C E F X X Y) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison_precompose,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_comparison,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositePrimitive, Cochain.comp_add,
    dgFunctorCommaLeftUnit_firstPrimitive,
    dgFunctorCommaLeftUnit_secondPrimitive, zero_add]
/-- 右単位と実合成の比較 cochain も、元の同じ比較 cochain。 -/
lemma dgFunctorCommaRightUnit_comparison :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison R C E F X Y _
      (dgFunctorCommaRightUnitInsertion R C E F X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition R C E F X Y Y) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison_precompose,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_comparison,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositePrimitive, Cochain.comp_add,
    dgFunctorCommaRightUnit_firstPrimitive,
    dgFunctorCommaRightUnit_secondPrimitive, add_zero]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
