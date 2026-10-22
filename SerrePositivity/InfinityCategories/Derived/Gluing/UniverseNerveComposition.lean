module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseNerveMap

/-! 共通宇宙の nerve は元の dg 関手の合成を、同じ全単体を保持して送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w r s
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {R : Type u} [CommRing R] {C : Type v} {D : Type w} {E : Type r}
  [DGCategory R C] [DGCategory R D] [DGCategory R E]

lemma dgGluingUniverseNerveMap_comp (F : DGFunctor R C D) (G : DGFunctor R D E) :
    dgGluingUniverseNerveMap.{u, v, w, max u v w r s} F ≫
        dgGluingUniverseNerveMap.{u, w, r, max u v w r s} G =
      dgGluingUniverseNerveMap.{u, v, r, max u v w r s} (F.comp G) := by
  ext n a
  apply ULift.ext
  apply Simplex.ext
  exact (SimplexData.map_comp a.down.toSimplexData F G).symm

end SerrePositivity.InfinityCategories
