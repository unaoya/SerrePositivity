module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DiagramRightPrismFamily
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty

/-!
概要：頂点を持たない元の図式形状との積は、任意の試験族について始対象。
方針：積の頂点の右成分から元の形状の頂点を取り出して矛盾する。
規約：試験族の有限性や非空性を仮定しない。
使われ方：有限半順序図式の単一 filtered 表示の空形状の基底。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
/-- 概要：頂点を持たない元の形状との持ち上げた積は始対象。
方針：元の頂点の非存在。規約：任意の全試験族。使われ方：空の全 C 族と全円柱。 -/
def emptyShapeTensorIsInitial {K : SSet.{u}} (hK : ¬ K.Nonempty) (T : SSet.{u + 1}) :
    IsInitial (T ⊗ (SSet.uliftFunctor.{u + 1, u}).obj K) :=
  SSet.isInitialOfNotNonempty (by
    rintro ⟨⟨_, k⟩⟩
    exact hK ⟨k.down⟩)
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
