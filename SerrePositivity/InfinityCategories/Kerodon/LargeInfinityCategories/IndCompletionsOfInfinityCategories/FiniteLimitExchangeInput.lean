module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.CoherentFilteredLimitExchange
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite

/-!
概要：F2N-5 の有限極限交換に必要な、未提供の一般 coherent 定理を明示する。
方針：F1b の元の点ごとの native 余極限と全錐を量化する述語をそのまま束ねる。
規約：この入力の存在を主張せず、公理や instance として補わない。
使われ方：Ind の有限極限と安定性への条件付き入力。F1b の提供後に実証拠を渡す。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 全有限形状と一般 coherent filtered 図式に対する、F1b 提供待ちの交換定理。 -/
structure IndFiniteLimitExchangeInput : Prop where
  exchange (K : SSet.{u}) [K.Finite] : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.CoherentFilteredLimitExchangeShape K

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
