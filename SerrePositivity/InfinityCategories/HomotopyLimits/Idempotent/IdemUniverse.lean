module

public import SerrePositivity.InfinityCategories.Core.Idempotent.ScalarUniverse
public import SerrePositivity.InfinityCategories.Core.Idempotent.Walking
public import SerrePositivity.InfinityCategories.HomotopyLimits.LiftedShapeNerveIso
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictNerveMaps

/-!
概要：持ち上げた元の全 Idem と、大きい宇宙の元の全 Idem の厳密な同型。
方針：元の二元モノイドの宇宙変更を全射に適用し、厳密な逆関手から nerve 同型を作る。
規約：全 coherent 図式を扱い、頂点や一つの自己射だけへ縮約しない。
使われ方：前層 ∞ 圏の小さい余極限からの冪等完備性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 持ち上げた元の Idem 圏の射を、同じ二元の大きい宇宙の射へ移す。 -/
def walkingIdemUniverseUp : AsSmall.{v} WalkingIdem.{u} ⥤ WalkingIdem.{max u v} where
  obj _ := walkingObject
  map f := walkingScalarUniverse f.down
  map_id _ := rfl
  map_comp f g := (walkingScalarUniverse.map_mul g.down f.down)

/-- 大きい宇宙の元の Idem 圏を、持ち上げた元の圏へ厳密に戻す。 -/
def walkingIdemUniverseDown : WalkingIdem.{max u v} ⥤ AsSmall.{v} WalkingIdem.{u} where
  obj _ := AsSmall.up.obj walkingObject
  map f := ULift.up (walkingScalarUniverse f)
  map_id _ := rfl
  map_comp f g := congrArg ULift.up (walkingScalarUniverse.map_mul g f)

/-- 元の全 Idem 図式の持ち上げは、大きい宇宙の同じ全 Idem と厳密に同型。 -/
def idemShapeUniverseIso :
    (SSet.uliftFunctor.{v, u}).obj IdemShape.{u} ≅ IdemShape.{max u v} := by
  have hFG : walkingIdemUniverseUp.{u, v} ⋙ walkingIdemUniverseDown = 𝟭 _ := by
    refine CategoryTheory.Functor.ext (fun P ↦ ?_) (fun P Q f ↦ ?_)
    · cases P with | up P => cases P with | up P => cases P; rfl
    · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      apply ULift.ext
      exact walkingScalarUniverse_inverse f.down
  have hGF : walkingIdemUniverseDown.{u, v} ⋙ walkingIdemUniverseUp = 𝟭 _ := by
    refine CategoryTheory.Functor.ext (fun P ↦ ?_) (fun P Q f ↦ ?_)
    · cases P with | up P => cases P; rfl
    · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      exact walkingScalarUniverse_inverse f
  exact HomotopyLimits.nerveAsSmallIso WalkingIdem ≪≫
    HomotopyLimits.nerveIsoOfStrictInverse _ _ hFG hGF

end SerrePositivity.InfinityCategories.F2.Idempotent
