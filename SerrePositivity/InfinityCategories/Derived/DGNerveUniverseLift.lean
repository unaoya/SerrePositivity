module
public import SerrePositivity.InfinityCategories.Derived.DGUniverseLift
public import SerrePositivity.InfinityCategories.DGNerve.Functor

/-! # dg nerve と対象宇宙の持ち上げの可換性

概要：対象を ULift した dg 圏の nerve は元の nerve の単体集合としての ULift と同型。
方針：各単体を上げ下げする dg 関手で写し、全ての単調写像との可換性を使う。
規約：単体集合の実同型。使われ方：異なる対象宇宙にある Yoneda 模型の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 対象宇宙の持ち上げと nerve は単体集合の実同型で可換。 -/
def dgNerveUniverseLiftIso :
    (SSet.uliftFunctor.{w, max u v}).obj (dgNerve A D) ≅
      dgNerve A (DGUniverseLift.{v, w} D) where
  hom := {
    app _ := ↾fun s => s.down.map (dgUniverseLiftUp A D)
    naturality _ _ α := by
      ext s
      apply Simplex.ext
      exact SimplexData.map_pullback s.down.toSimplexData (dgUniverseLiftUp A D)
        α.unop.toOrderHom }
  inv := {
    app _ := ↾fun s => ULift.up (s.map (dgUniverseLiftDown A D))
    naturality _ _ α := by
      ext s
      apply ULift.ext
      apply Simplex.ext
      exact SimplexData.map_pullback s.toSimplexData (dgUniverseLiftDown A D)
        α.unop.toOrderHom }
  hom_inv_id := by
    ext n s
    apply ULift.ext
    apply Simplex.ext
    change (s.down.toSimplexData.map (dgUniverseLiftUp A D)).map
      (dgUniverseLiftDown A D) = s.down.toSimplexData
    rw [← SimplexData.map_comp, dgUniverseLiftUp_comp_down.{u, v, w} A D, SimplexData.map_id]
  inv_hom_id := by
    ext n s
    apply Simplex.ext
    change (s.toSimplexData.map (dgUniverseLiftDown A D)).map
      (dgUniverseLiftUp A D) = s.toSimplexData
    rw [← SimplexData.map_comp, dgUniverseLiftDown_comp_up.{u, v, w} A D, SimplexData.map_id]

end SerrePositivity.InfinityCategories
