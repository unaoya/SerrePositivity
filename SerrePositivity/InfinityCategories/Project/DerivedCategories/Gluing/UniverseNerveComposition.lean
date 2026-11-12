module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseNerveMap

/-! 共通宇宙の nerve は元の dg 関手の合成を、同じ全単体を保持して送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w r s
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {C : Type v} {D : Type w} {E : Type r}
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]

lemma dgGluingUniverseNerveMap_comp (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C D) (G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerveMap.{u, v, w, max u v w r s} F ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerveMap.{u, w, r, max u v w r s} G =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerveMap.{u, v, r, max u v w r s} (F.comp G) := by
  ext n a
  apply ULift.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_comp a.down.toSimplexData F G).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
