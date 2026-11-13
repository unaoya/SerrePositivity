module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGFunctors.DGFunctorCommaUnitComparison
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
/-- 全 Hom 複体上の実左単位律。 -/
lemma dgFunctorComma_id_comp :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaLeftUnitInsertion R C E F X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition R C E F X X Y = 𝟙 _ := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHom_ext R C E F X Y
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_source, Category.id_comp]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.parameterEnriched_leftUnit (Complex R) C X.source Y.source
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity R C E F X)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R C E F X X)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R C E F X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_source R C E F X)
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_replacement, Category.id_comp]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.parameterEnriched_leftUnit (Complex R) E
      X.replacement Y.replacement
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity R C E F X)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X X)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_replacement R C E F X)
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaLeftUnit_comparison,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison_id]
/-- 全 Hom 複体上の実右単位律。 -/
lemma dgFunctorComma_comp_id :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaRightUnitInsertion R C E F X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition R C E F X Y Y = 𝟙 _ := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHom_ext R C E F X Y
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_source, Category.id_comp]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.parameterEnriched_rightUnit (Complex R) C X.source Y.source
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity R C E F Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R C E F Y Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R C E F X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_source R C E F Y)
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_replacement, Category.id_comp]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.parameterEnriched_rightUnit (Complex R) E
      X.replacement Y.replacement
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity R C E F Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F Y Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_replacement R C E F Y)
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaRightUnit_comparison,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison_id]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
