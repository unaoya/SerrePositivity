module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveUniverseLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLiftFunctor

/-! # 異なる対象宇宙を持つ dg 関手の nerve

概要：始域と終域の nerve を共通宇宙へ上げ、任意の dg 関手を実単体的写像へ送る。
方針：各単体に元の dg 関手を適用し、対象を上げた関手との可換性を照合する。
規約：元の二つの対象宇宙を等しいと仮定しない。使われ方：dg Yoneda の全加群圏への像。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} {E : Type w}
variable [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [DGCategory A E]

/-- 異なる対象宇宙の dg 関手の nerve を共通宇宙で定義する。 -/
def dgNerveUniverseMap (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) :
    (SSet.uliftFunctor.{w, max u v}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) ⟶
      (SSet.uliftFunctor.{v, max u w}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A E) where
  app _ := ↾fun s => ULift.up (s.down.map F)
  naturality _ _ α := by
    ext s
    apply ULift.ext
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map_pullback s.down.toSimplexData F α.unop.toOrderHom

/-- 宇宙を上げた関手の nerve と元の関手の宇宙移送は実同型で可換。 -/
lemma dgNerveUniverseMap_lift (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) :
    dgNerveUniverseMap F ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseLiftIso.{u, w, v} A E).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseLiftIso.{u, v, w} A D).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, v, w, w, v} F) := by
  ext n s
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  change (s.down.toSimplexData.map F).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, w, v} A E) =
    (s.down.toSimplexData.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, v, w} A D)).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, v, w, w, v} F)
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp_comp_functor.{u, v, w, w, v} F]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
