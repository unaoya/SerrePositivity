module
public import SerrePositivity.InfinityCategories.Derived.DGNerveUniverseMap

/-! 任意の追加宇宙を含む共通宇宙で、元の dg 関手の全単体を保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w r
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable {R : Type u} [CommRing R] {C : Type v} {D : Type w}
  [DGCategory R C] [DGCategory R D]

def dgGluingUniverseNerveMap (F : DGFunctor R C D) :
    (SSet.uliftFunctor.{max w r, max u v}).obj (dgNerve R C) ⟶
      (SSet.uliftFunctor.{max v r, max u w}).obj (dgNerve R D) where
  app _ := ↾fun s => ULift.up (s.down.map F)
  naturality _ _ α := by
    ext s
    apply ULift.ext
    apply Simplex.ext
    exact SimplexData.map_pullback s.down.toSimplexData F α.unop.toOrderHom

lemma dgGluingUniverseNerveMap_vertex (F : DGFunctor R C D) (x : C) :
    (dgGluingUniverseNerveMap.{u, v, w, r} F).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex x)) = ULift.up (Simplex.vertex (F.obj x)) := by
  apply ULift.ext
  apply (Simplex.vertexEquiv (A := R) (D := D)).injective
  rfl

end SerrePositivity.InfinityCategories
