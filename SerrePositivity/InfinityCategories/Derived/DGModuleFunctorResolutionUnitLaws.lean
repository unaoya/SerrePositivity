module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionUnitComparison
/-!
概要：出力分解の全 Hom 複体上で、実合成と実単位の左右単位律を証明する。
方針：二つの実射影と比較 cochain の一致から、mapping cocone への実射の一意性を使う。
規約：次数零への制限ではない。使われ方：出力分解 dg 圏の実単位律。
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
/-- 全 Hom 複体上の実左単位律。 -/
lemma dgModuleFunctorResolution_id_comp :
    dgModuleFunctorResolutionLeftUnitInsertion R C E F X Y ≫
      dgModuleFunctorResolutionComposition R C E F X X Y = 𝟙 _ := by
  apply dgModuleFunctorResolutionHom_ext R C E F X Y
  · rw [Category.assoc, dgModuleFunctorResolutionComposition_source, Category.id_comp]
    exact parameterEnriched_leftUnit (Complex R) C X.source Y.source
      (dgModuleFunctorResolutionIdentity R C E F X)
      (dgModuleFunctorResolutionSourceHomMap R C E F X X)
      (dgModuleFunctorResolutionSourceHomMap R C E F X Y)
      (dgModuleFunctorResolutionIdentity_source R C E F X)
  · rw [Category.assoc, dgModuleFunctorResolutionComposition_replacement, Category.id_comp]
    exact parameterEnriched_leftUnit (Complex R) (RightModule R E)
      X.replacement.val Y.replacement.val
      (dgModuleFunctorResolutionIdentity R C E F X)
      (dgModuleFunctorResolutionReplacementHomMap R C E F X X)
      (dgModuleFunctorResolutionReplacementHomMap R C E F X Y)
      (dgModuleFunctorResolutionIdentity_replacement R C E F X)
  · rw [dgModuleFunctorResolutionLeftUnit_comparison,
      dgModuleFunctorResolutionHomComparison_id]
/-- 全 Hom 複体上の実右単位律。 -/
lemma dgModuleFunctorResolution_comp_id :
    dgModuleFunctorResolutionRightUnitInsertion R C E F X Y ≫
      dgModuleFunctorResolutionComposition R C E F X Y Y = 𝟙 _ := by
  apply dgModuleFunctorResolutionHom_ext R C E F X Y
  · rw [Category.assoc, dgModuleFunctorResolutionComposition_source, Category.id_comp]
    exact parameterEnriched_rightUnit (Complex R) C X.source Y.source
      (dgModuleFunctorResolutionIdentity R C E F Y)
      (dgModuleFunctorResolutionSourceHomMap R C E F Y Y)
      (dgModuleFunctorResolutionSourceHomMap R C E F X Y)
      (dgModuleFunctorResolutionIdentity_source R C E F Y)
  · rw [Category.assoc, dgModuleFunctorResolutionComposition_replacement, Category.id_comp]
    exact parameterEnriched_rightUnit (Complex R) (RightModule R E)
      X.replacement.val Y.replacement.val
      (dgModuleFunctorResolutionIdentity R C E F Y)
      (dgModuleFunctorResolutionReplacementHomMap R C E F Y Y)
      (dgModuleFunctorResolutionReplacementHomMap R C E F X Y)
      (dgModuleFunctorResolutionIdentity_replacement R C E F Y)
  · rw [dgModuleFunctorResolutionRightUnit_comparison,
      dgModuleFunctorResolutionHomComparison_id]
end SerrePositivity.InfinityCategories
