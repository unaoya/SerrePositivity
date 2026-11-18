module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveAsSmall
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightMapMono

/-!
# 対象と射の宇宙が異なる圏の nerve の単射性

概要：対象上単射な忠実関手の nerve の単射性を、異なる対象・射の宇宙へ移す。
方針：既存の小圏版を AsSmall に適用し、同じ射列の up・down で元へ戻す。
規約：小圏版の証明を再実装せず、元の全単体を保持する。
使われ方：zigzag 圏の語の包含による graph の単射性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.CategoryTheory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- 小圏版を同じ元の射列の宇宙比較で一般の圏へ移す。 -/
lemma nerveMap_mono_of_faithful (F : C ⥤ D) [F.Faithful]
    (hF : Function.Injective F.obj) : Mono (nerveMap F) := by
  let G : AsSmall.{0} C ⥤ AsSmall.{0} D := AsSmall.down ⋙ F ⋙ AsSmall.up
  have hG : Function.Injective G.obj := by
    intro X Y h
    apply ULift.ext
    apply hF
    exact congrArg ULift.down h
  have : G.Faithful :=
    { map_injective := by
        intro X Y f g h
        apply ULift.ext
        apply F.map_injective
        exact congrArg ULift.down h }
  have : Mono (nerveMap G) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveMap_mono_of_faithful G hG
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro σ τ h
  change σ ⋙ F = τ ⋙ F at h
  have hs : (σ ⋙ AsSmall.up) ⋙ G = (τ ⋙ AsSmall.up) ⋙ G :=
    congrArg (fun H : Fin (n.unop.len + 1) ⥤ D => H ⋙ AsSmall.up) h
  have ht : σ ⋙ AsSmall.up = τ ⋙ AsSmall.up :=
    CategoryTheory.injective_of_mono ((nerveMap G).app n) hs
  have hd := congrArg (fun H : Fin (n.unop.len + 1) ⥤ AsSmall.{0} C => H ⋙ AsSmall.down) ht
  simpa only [Functor.assoc, _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveAsSmall.up_down, Functor.comp_id] using hd

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
