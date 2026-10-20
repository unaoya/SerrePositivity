module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionComparisonNaturality
public import SerrePositivity.InfinityCategories.Derived.EnrichedCochainUnit
/-!
概要：出力分解の実合成へ単位を挿入したとき、同じ全比較 cochain を回収する。
方針：二項の一方を零化し、もう一方を実豊穣単位律で回収する。
規約：全 Hom 複体上の等式。使われ方：分解 dg 圏の左右単位律。
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
  (X Y : DGModuleFunctorResolutionObject R C E F)
/-- 元の dg 関手への実像も、同じ単位を保つ。 -/
lemma dgModuleFunctorResolutionIdentity_image :
    dgModuleFunctorResolutionIdentity R C E F X ≫
      dgModuleFunctorResolutionImageHomMap R C E F X X =
        eId (Complex R) (F.obj X.source) := by
  rw [dgModuleFunctorResolutionImageHomMap, ← Category.assoc,
    dgModuleFunctorResolutionIdentity_source, F.map_id]
/-- 実左単位を全 Hom tensor の第一因子へ挿入する。 -/
def dgModuleFunctorResolutionLeftUnitInsertion :
    dgModuleFunctorResolutionHomComplex R C E F X Y ⟶
      dgModuleFunctorResolutionHomComplex R C E F X X ⊗
        dgModuleFunctorResolutionHomComplex R C E F X Y :=
  (λ_ _).inv ≫ dgModuleFunctorResolutionIdentity R C E F X ▷ _
/-- 実右単位を全 Hom tensor の第二因子へ挿入する。 -/
def dgModuleFunctorResolutionRightUnitInsertion :
    dgModuleFunctorResolutionHomComplex R C E F X Y ⟶
      dgModuleFunctorResolutionHomComplex R C E F X Y ⊗
        dgModuleFunctorResolutionHomComplex R C E F Y Y :=
  (ρ_ _).inv ≫ _ ◁ dgModuleFunctorResolutionIdentity R C E F Y
/-- 左単位では、第一比較項は零となる。 -/
lemma dgModuleFunctorResolutionLeftUnit_firstPrimitive :
    (Cochain.ofHom (dgModuleFunctorResolutionLeftUnitInsertion R C E F X Y)).comp
      (dgModuleFunctorResolutionFirstCompositePrimitive R C E F X X Y) (zero_add (-1)) =
        0 := by
  rw [dgModuleFunctorResolutionFirstCompositePrimitive,
    ← Cochain.comp_assoc_of_first_is_zero_cochain]
  have hz : (Cochain.ofHom (dgModuleFunctorResolutionIdentity R C E F X)).comp
      (dgModuleFunctorResolutionPrimitive R C E F X X) (zero_add (-1)) = 0 :=
    dgModuleFunctorResolutionIdentity_comparison R C E F X
  rw [dgModuleFunctorResolutionLeftUnitInsertion,
    complexLeftUnitInsertion_rightTensor_zero _ _ _ hz, Cochain.zero_comp]
/-- 左単位では、第二比較項が元の同じ比較 cochain を回収する。 -/
lemma dgModuleFunctorResolutionLeftUnit_secondPrimitive :
    (Cochain.ofHom (dgModuleFunctorResolutionLeftUnitInsertion R C E F X Y)).comp
      (dgModuleFunctorResolutionSecondCompositePrimitive R C E F X X Y) (zero_add (-1)) =
        dgModuleFunctorResolutionPrimitive R C E F X Y := by
  exact enrichedCochain_leftUnit (RightModule R E) X.replacement.val (F.obj Y.source)
    (dgModuleFunctorResolutionIdentity R C E F X)
    (dgModuleFunctorResolutionReplacementHomMap R C E F X X)
    (dgModuleFunctorResolutionIdentity_replacement R C E F X) (-1)
    (dgModuleFunctorResolutionPrimitive R C E F X Y)
/-- 右単位では、第一比較項が元の同じ比較 cochain を回収する。 -/
lemma dgModuleFunctorResolutionRightUnit_firstPrimitive :
    (Cochain.ofHom (dgModuleFunctorResolutionRightUnitInsertion R C E F X Y)).comp
      (dgModuleFunctorResolutionFirstCompositePrimitive R C E F X Y Y) (zero_add (-1)) =
        dgModuleFunctorResolutionPrimitive R C E F X Y := by
  exact enrichedCochain_rightUnit (RightModule R E) X.replacement.val (F.obj Y.source)
    (dgModuleFunctorResolutionIdentity R C E F Y)
    (dgModuleFunctorResolutionImageHomMap R C E F Y Y)
    (dgModuleFunctorResolutionIdentity_image R C E F Y) (-1)
    (dgModuleFunctorResolutionPrimitive R C E F X Y)
/-- 右単位では、第二比較項は零となる。 -/
lemma dgModuleFunctorResolutionRightUnit_secondPrimitive :
    (Cochain.ofHom (dgModuleFunctorResolutionRightUnitInsertion R C E F X Y)).comp
      (dgModuleFunctorResolutionSecondCompositePrimitive R C E F X Y Y) (zero_add (-1)) =
        0 := by
  rw [dgModuleFunctorResolutionSecondCompositePrimitive,
    ← Cochain.comp_assoc_of_first_is_zero_cochain]
  have hz : (Cochain.ofHom (dgModuleFunctorResolutionIdentity R C E F Y)).comp
      (dgModuleFunctorResolutionPrimitive R C E F Y Y) (zero_add (-1)) = 0 :=
    dgModuleFunctorResolutionIdentity_comparison R C E F Y
  rw [dgModuleFunctorResolutionRightUnitInsertion,
    complexRightUnitInsertion_leftTensor_zero _ _ _ hz, Cochain.zero_comp]
/-- 左単位と実合成の比較 cochain は、元の同じ比較 cochain。 -/
lemma dgModuleFunctorResolutionLeftUnit_comparison :
    dgModuleFunctorResolutionHomComparison R C E F X Y _
      (dgModuleFunctorResolutionLeftUnitInsertion R C E F X Y ≫
        dgModuleFunctorResolutionComposition R C E F X X Y) =
      dgModuleFunctorResolutionPrimitive R C E F X Y := by
  rw [dgModuleFunctorResolutionHomComparison_precompose,
    dgModuleFunctorResolutionComposition_comparison,
    dgModuleFunctorResolutionCompositePrimitive, Cochain.comp_add,
    dgModuleFunctorResolutionLeftUnit_firstPrimitive,
    dgModuleFunctorResolutionLeftUnit_secondPrimitive, zero_add]
/-- 右単位と実合成の比較 cochain も、元の同じ比較 cochain。 -/
lemma dgModuleFunctorResolutionRightUnit_comparison :
    dgModuleFunctorResolutionHomComparison R C E F X Y _
      (dgModuleFunctorResolutionRightUnitInsertion R C E F X Y ≫
        dgModuleFunctorResolutionComposition R C E F X Y Y) =
      dgModuleFunctorResolutionPrimitive R C E F X Y := by
  rw [dgModuleFunctorResolutionHomComparison_precompose,
    dgModuleFunctorResolutionComposition_comparison,
    dgModuleFunctorResolutionCompositePrimitive, Cochain.comp_add,
    dgModuleFunctorResolutionRightUnit_firstPrimitive,
    dgModuleFunctorResolutionRightUnit_secondPrimitive, add_zero]
end SerrePositivity.InfinityCategories
