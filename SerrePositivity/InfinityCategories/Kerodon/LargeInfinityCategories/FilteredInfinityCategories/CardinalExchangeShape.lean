module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.CoherentFilteredPosetExchange
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CardinalChangeUniverse
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NervePosetUniverse

/-!
概要：指定形状の μ-filtered な全錐交換を、形状の同型と元の poset の宇宙持ち上げへ輸送する。
方針：元の全余錐の前合成と全頂点錐の極限性を保ち、実証済みの poset 交換を使う。
規約：有限交換の仮定を再利用せず、元の μ-filtered 条件を保持する。
使われ方：N の Hom 錐族の反対形状に対する実証拠。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories


/-- 指定形状の全極限錐が、元の一般 μ-filtered 全錐族の指定点ごとの余極限で保たれること。 -/
def CardinalFilteredLimitExchangeShape (μ : Cardinal.{u}) (K : SSet.{u}) : Prop :=
  ∀ (B : SSet.{u}) [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ B]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶
      (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u + 1})
        ((SSet.uliftFunctor.{u + 1, u}).obj K))).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F), _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.IsPointwiseColimitCone c →
      (∀ b : B _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone (F.app
        (Opposite.op ⦋0⦌) (ULift.up b)))) → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone c.vertex)

/-- 同型な形状の交換は、元の全余錐を保つ前合成によって輸送される。 -/
lemma CardinalFilteredLimitExchangeShape.of_iso {μ : Cardinal.{u}} {L K : SSet.{u}}
    (e : L ≅ K) (h : CardinalFilteredLimitExchangeShape μ L) :
    CardinalFilteredLimitExchangeShape μ K := by
  intro B hB hμ F c hc hF
  let r := (SSet.uliftFunctor.{u + 1, u}).map e.hom
  let q := (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u + 1})) r)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}
  have ht := h B (F ≫ q) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone q c)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pointwiseColimitCocone_precomp c hc _)
    (fun b ↦ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.isLimitCone_functorVertexCone_reindex_iff r
      (F.app (Opposite.op ⦋0⦌) (ULift.up b))).mpr (hF b))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.mapJoinCocone_vertex] at ht
  exact (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.isLimitCone_functorVertexCone_reindex_iff r c.vertex).mp ht

/-- 実証済みの小さい poset の全錐交換を、指定形状の述語として公開する。 -/
lemma cardinalFilteredLimitExchangeShape_poset
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ) (I : Type u) [PartialOrder I] (hI : HasCardinalLT I μ) :
    CardinalFilteredLimitExchangeShape μ (nerve I) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.coherentCardinalFilteredLimitExchange_poset h I hI

/-- N の大きい Hom 錐の元の反対形状に対する、同じ持ち上げた濃度での全交換の実証拠。 -/
lemma cardinalFilteredLimitExchangeShape_ulift_poset_op
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ) (I : Type u) [PartialOrder I] (hI : HasCardinalLT I μ) :
    CardinalFilteredLimitExchangeShape (Cardinal.lift.{v} μ)
      (((SSet.uliftFunctor.{v, u}).obj (nerve I)).op) := by
  have : Fact (Cardinal.lift.{v} κ).IsRegular := ⟨(Fact.out : κ.IsRegular).lift⟩
  have : Fact (Cardinal.lift.{v} μ).IsRegular := ⟨(Fact.out : μ.IsRegular).lift⟩
  have hi : HasCardinalLT (ULift.{v} (OrderDual I)) (Cardinal.lift.{v} μ) := by
    have hd : HasCardinalLT (OrderDual I) μ := hI
    simpa only [hasCardinalLT_lift_iff, hasCardinalLT_ulift_iff] using hd
  exact (cardinalFilteredLimitExchangeShape_poset h.lift _ hi).of_iso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nervePosetUniverseOppositeIso.{u, v} I).symm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
