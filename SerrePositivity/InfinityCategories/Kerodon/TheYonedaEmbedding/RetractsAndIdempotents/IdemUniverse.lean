module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.ScalarUniverse
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Walking
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.LiftedShapeNerveIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictNerveMaps

/-!
概要：持ち上げた元の全 Idem と、大きい宇宙の元の全 Idem の厳密な同型。
方針：元の二元モノイドの宇宙変更を全射に適用し、厳密な逆関手から nerve 同型を作る。
規約：全 coherent 図式を扱い、頂点や一つの自己射だけへ縮約しない。
使われ方：前層 ∞ 圏の小さい余極限からの冪等完備性。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 持ち上げた元の Idem 圏の射を、同じ二元の大きい宇宙の射へ移す。 -/
def walkingIdemUniverseUp : AsSmall.{v} _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingIdem.{u} ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingIdem.{max u v} where
  obj _ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingObject
  map f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalarUniverse f.down
  map_id _ := rfl
  map_comp f g := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalarUniverse.map_mul g.down f.down)

/-- 大きい宇宙の元の Idem 圏を、持ち上げた元の圏へ厳密に戻す。 -/
def walkingIdemUniverseDown : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingIdem.{max u v} ⥤ AsSmall.{v} _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingIdem.{u} where
  obj _ := AsSmall.up.obj _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingObject
  map f := ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalarUniverse f)
  map_id _ := rfl
  map_comp f g := congrArg ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalarUniverse.map_mul g f)

/-- 元の全 Idem 図式の持ち上げは、大きい宇宙の同じ全 Idem と厳密に同型。 -/
def idemShapeUniverseIso :
    (SSet.uliftFunctor.{v, u}).obj _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemShape.{u} ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemShape.{max u v} := by
  have hFG : walkingIdemUniverseUp.{u, v} ⋙ walkingIdemUniverseDown = 𝟭 _ := by
    refine CategoryTheory.Functor.ext (fun P ↦ ?_) (fun P Q f ↦ ?_)
    · cases P with | up P => cases P with | up P => cases P; rfl
    · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      apply ULift.ext
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalarUniverse_inverse f.down
  have hGF : walkingIdemUniverseDown.{u, v} ⋙ walkingIdemUniverseUp = 𝟭 _ := by
    refine CategoryTheory.Functor.ext (fun P ↦ ?_) (fun P Q f ↦ ?_)
    · cases P with | up P => cases P; rfl
    · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalarUniverse_inverse f
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveAsSmallIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingIdem ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nerveIsoOfStrictInverse _ _ hFG hGF

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
