module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveUniverseMap

/-! 任意の追加宇宙を含む共通宇宙で、元の dg 関手の全単体を保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w r
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {C : Type v} {D : Type w}
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]

def dgGluingUniverseNerveMap (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C D) :
    (SSet.uliftFunctor.{max w r, max u v}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) ⟶
      (SSet.uliftFunctor.{max v r, max u w}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) where
  app _ := ↾fun s => ULift.up (s.down.map F)
  naturality _ _ α := by
    ext s
    apply ULift.ext
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map_pullback s.down.toSimplexData F α.unop.toOrderHom

lemma dgGluingUniverseNerveMap_vertex (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C D) (x : C) :
    (dgGluingUniverseNerveMap.{u, v, w, r} F).app (Opposite.op ⦋0⦌)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) = ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj x)) := by
  apply ULift.ext
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv (A := R) (D := D)).injective
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
