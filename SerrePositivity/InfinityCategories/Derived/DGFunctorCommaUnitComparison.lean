module
public import SerrePositivity.InfinityCategories.Derived.DGFunctorCommaComparisonNaturality
public import SerrePositivity.InfinityCategories.Derived.EnrichedCochainUnit
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y : DGFunctorCommaObject R C E F)
/-- 元の dg 関手への実像も、同じ単位を保つ。 -/
lemma dgFunctorCommaIdentity_image :
    dgFunctorCommaIdentity R C E F X ≫
      dgFunctorCommaImageHomMap R C E F X X =
        eId (Complex R) (F.obj X.source) := by
  rw [dgFunctorCommaImageHomMap, ← Category.assoc,
    dgFunctorCommaIdentity_source, F.map_id]
/-- 実左単位を全 Hom tensor の第一因子へ挿入する。 -/
def dgFunctorCommaLeftUnitInsertion :
    dgFunctorCommaHomComplex R C E F X Y ⟶
      dgFunctorCommaHomComplex R C E F X X ⊗
        dgFunctorCommaHomComplex R C E F X Y :=
  (λ_ _).inv ≫ dgFunctorCommaIdentity R C E F X ▷ _
/-- 実右単位を全 Hom tensor の第二因子へ挿入する。 -/
def dgFunctorCommaRightUnitInsertion :
    dgFunctorCommaHomComplex R C E F X Y ⟶
      dgFunctorCommaHomComplex R C E F X Y ⊗
        dgFunctorCommaHomComplex R C E F Y Y :=
  (ρ_ _).inv ≫ _ ◁ dgFunctorCommaIdentity R C E F Y
/-- 左単位では、第一比較項は零となる。 -/
lemma dgFunctorCommaLeftUnit_firstPrimitive :
    (Cochain.ofHom (dgFunctorCommaLeftUnitInsertion R C E F X Y)).comp
      (dgFunctorCommaFirstCompositePrimitive R C E F X X Y) (zero_add (-1)) =
        0 := by
  rw [dgFunctorCommaFirstCompositePrimitive,
    ← Cochain.comp_assoc_of_first_is_zero_cochain]
  have hz : (Cochain.ofHom (dgFunctorCommaIdentity R C E F X)).comp
      (dgFunctorCommaPrimitive R C E F X X) (zero_add (-1)) = 0 :=
    dgFunctorCommaIdentity_comparison R C E F X
  rw [dgFunctorCommaLeftUnitInsertion,
    complexLeftUnitInsertion_rightTensor_zero _ _ _ hz, Cochain.zero_comp]
/-- 左単位では、第二比較項が元の同じ比較 cochain を回収する。 -/
lemma dgFunctorCommaLeftUnit_secondPrimitive :
    (Cochain.ofHom (dgFunctorCommaLeftUnitInsertion R C E F X Y)).comp
      (dgFunctorCommaSecondCompositePrimitive R C E F X X Y) (zero_add (-1)) =
        dgFunctorCommaPrimitive R C E F X Y := by
  exact enrichedCochain_leftUnit E X.replacement (F.obj Y.source)
    (dgFunctorCommaIdentity R C E F X)
    (dgFunctorCommaReplacementHomMap R C E F X X)
    (dgFunctorCommaIdentity_replacement R C E F X) (-1)
    (dgFunctorCommaPrimitive R C E F X Y)
/-- 右単位では、第一比較項が元の同じ比較 cochain を回収する。 -/
lemma dgFunctorCommaRightUnit_firstPrimitive :
    (Cochain.ofHom (dgFunctorCommaRightUnitInsertion R C E F X Y)).comp
      (dgFunctorCommaFirstCompositePrimitive R C E F X Y Y) (zero_add (-1)) =
        dgFunctorCommaPrimitive R C E F X Y := by
  exact enrichedCochain_rightUnit E X.replacement (F.obj Y.source)
    (dgFunctorCommaIdentity R C E F Y)
    (dgFunctorCommaImageHomMap R C E F Y Y)
    (dgFunctorCommaIdentity_image R C E F Y) (-1)
    (dgFunctorCommaPrimitive R C E F X Y)
/-- 右単位では、第二比較項は零となる。 -/
lemma dgFunctorCommaRightUnit_secondPrimitive :
    (Cochain.ofHom (dgFunctorCommaRightUnitInsertion R C E F X Y)).comp
      (dgFunctorCommaSecondCompositePrimitive R C E F X Y Y) (zero_add (-1)) =
        0 := by
  rw [dgFunctorCommaSecondCompositePrimitive,
    ← Cochain.comp_assoc_of_first_is_zero_cochain]
  have hz : (Cochain.ofHom (dgFunctorCommaIdentity R C E F Y)).comp
      (dgFunctorCommaPrimitive R C E F Y Y) (zero_add (-1)) = 0 :=
    dgFunctorCommaIdentity_comparison R C E F Y
  rw [dgFunctorCommaRightUnitInsertion,
    complexRightUnitInsertion_leftTensor_zero _ _ _ hz, Cochain.zero_comp]
/-- 左単位と実合成の比較 cochain は、元の同じ比較 cochain。 -/
lemma dgFunctorCommaLeftUnit_comparison :
    dgFunctorCommaHomComparison R C E F X Y _
      (dgFunctorCommaLeftUnitInsertion R C E F X Y ≫
        dgFunctorCommaComposition R C E F X X Y) =
      dgFunctorCommaPrimitive R C E F X Y := by
  rw [dgFunctorCommaHomComparison_precompose,
    dgFunctorCommaComposition_comparison,
    dgFunctorCommaCompositePrimitive, Cochain.comp_add,
    dgFunctorCommaLeftUnit_firstPrimitive,
    dgFunctorCommaLeftUnit_secondPrimitive, zero_add]
/-- 右単位と実合成の比較 cochain も、元の同じ比較 cochain。 -/
lemma dgFunctorCommaRightUnit_comparison :
    dgFunctorCommaHomComparison R C E F X Y _
      (dgFunctorCommaRightUnitInsertion R C E F X Y ≫
        dgFunctorCommaComposition R C E F X Y Y) =
      dgFunctorCommaPrimitive R C E F X Y := by
  rw [dgFunctorCommaHomComparison_precompose,
    dgFunctorCommaComposition_comparison,
    dgFunctorCommaCompositePrimitive, Cochain.comp_add,
    dgFunctorCommaRightUnit_firstPrimitive,
    dgFunctorCommaRightUnit_secondPrimitive, add_zero]
end SerrePositivity.InfinityCategories
