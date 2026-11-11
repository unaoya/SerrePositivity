module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FiberHomotopyProjection
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ArrowIdentityComposition

/-!
概要：定値終点へのホモトピーの終点成分が恒等なら、そこへの任意の射の像を成分に同定する。
方針：自然性の四角形で二つの恒等成分を Arrow として消去する。
規約：端点の表示を保つ。使われ方：選んだ終対象錐と普遍評価との照合。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
/-- 終点成分が恒等なら、そこへ入る任意の射の像は始点での同じホモトピー成分。 -/
lemma roofHomotopyToConstant_component_arrow {E B : SSet.{u}} [Quasicategory E]
    {p : E ⟶ B} (b : B _⦋0⦌) (H : SSet.Homotopy p (SSet.const b))
    {a t : E _⦋0⦌} (e : (SSet.HomotopyCategory.mk a : hoFunctor.obj E) ⟶
      SSet.HomotopyCategory.mk t)
    (ht : Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints H.h H.h₀ H.h₁).app
      (SSet.HomotopyCategory.mk t)) = Arrow.mk (𝟙 (SSet.HomotopyCategory.mk b))) :
    Arrow.mk ((hoFunctor.map p).toFunctor.map e) =
      Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints H.h H.h₀ H.h₁).app
        (SSet.HomotopyCategory.mk a)) := by
  let η := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints H.h H.h₀ H.h₁
  have hg := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoConst_map_arrow b e
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowMk_comp_of_right_identity ((hoFunctor.map p).toFunctor.map e)
    (η.app (SSet.HomotopyCategory.mk t)) ht).symm.trans
      ((congrArg Arrow.mk (η.naturality e)).trans
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowMk_comp_of_right_identity (η.app (SSet.HomotopyCategory.mk a))
          ((hoFunctor.map (SSet.const b : E ⟶ B)).toFunctor.map e) hg))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
