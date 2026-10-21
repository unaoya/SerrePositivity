module
public import SerrePositivity.InfinityCategories.Derived.DGFunctorCommaUnitComparison
/-!
概要：commaの全 Hom 複体上で、実合成と実単位の左右単位律を証明する。
方針：二つの実射影と比較 cochain の一致から、mapping cocone への実射の一意性を使う。
規約：次数零への制限ではない。使われ方：comma dg 圏の実単位律。
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
/-- 全 Hom 複体上の実左単位律。 -/
lemma dgFunctorComma_id_comp :
    dgFunctorCommaLeftUnitInsertion R C E F X Y ≫
      dgFunctorCommaComposition R C E F X X Y = 𝟙 _ := by
  apply dgFunctorCommaHom_ext R C E F X Y
  · rw [Category.assoc, dgFunctorCommaComposition_source, Category.id_comp]
    exact parameterEnriched_leftUnit (Complex R) C X.source Y.source
      (dgFunctorCommaIdentity R C E F X)
      (dgFunctorCommaSourceHomMap R C E F X X)
      (dgFunctorCommaSourceHomMap R C E F X Y)
      (dgFunctorCommaIdentity_source R C E F X)
  · rw [Category.assoc, dgFunctorCommaComposition_replacement, Category.id_comp]
    exact parameterEnriched_leftUnit (Complex R) E
      X.replacement Y.replacement
      (dgFunctorCommaIdentity R C E F X)
      (dgFunctorCommaReplacementHomMap R C E F X X)
      (dgFunctorCommaReplacementHomMap R C E F X Y)
      (dgFunctorCommaIdentity_replacement R C E F X)
  · rw [dgFunctorCommaLeftUnit_comparison,
      dgFunctorCommaHomComparison_id]
/-- 全 Hom 複体上の実右単位律。 -/
lemma dgFunctorComma_comp_id :
    dgFunctorCommaRightUnitInsertion R C E F X Y ≫
      dgFunctorCommaComposition R C E F X Y Y = 𝟙 _ := by
  apply dgFunctorCommaHom_ext R C E F X Y
  · rw [Category.assoc, dgFunctorCommaComposition_source, Category.id_comp]
    exact parameterEnriched_rightUnit (Complex R) C X.source Y.source
      (dgFunctorCommaIdentity R C E F Y)
      (dgFunctorCommaSourceHomMap R C E F Y Y)
      (dgFunctorCommaSourceHomMap R C E F X Y)
      (dgFunctorCommaIdentity_source R C E F Y)
  · rw [Category.assoc, dgFunctorCommaComposition_replacement, Category.id_comp]
    exact parameterEnriched_rightUnit (Complex R) E
      X.replacement Y.replacement
      (dgFunctorCommaIdentity R C E F Y)
      (dgFunctorCommaReplacementHomMap R C E F Y Y)
      (dgFunctorCommaReplacementHomMap R C E F X Y)
      (dgFunctorCommaIdentity_replacement R C E F Y)
  · rw [dgFunctorCommaRightUnit_comparison,
      dgFunctorCommaHomComparison_id]
end SerrePositivity.InfinityCategories
