module

public import SerrePositivity.InfinityCategories.F2.Presentable.CoherentFilteredPosetExchange
public import SerrePositivity.InfinityCategories.F2.Presentable.CardinalChangeUniverse
public import SerrePositivity.InfinityCategories.F2.Presentable.NervePosetUniverse

/-!
概要：指定形状の μ-filtered な全錐交換を、形状の同型と元の poset の宇宙持ち上げへ輸送する。
方針：元の全余錐の前合成と全頂点錐の極限性を保ち、実証済みの poset 交換を使う。
規約：有限交換の仮定を再利用せず、元の μ-filtered 条件を保持する。
使われ方：N の Hom 錐族の反対形状に対する実証拠。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 指定形状の全極限錐が、元の一般 μ-filtered 全錐族の指定点ごとの余極限で保たれること。 -/
def CardinalFilteredLimitExchangeShape (μ : Cardinal.{u}) (K : SSet.{u}) : Prop :=
  ∀ (B : SSet.{u}) [Quasicategory B] [IsKappaFiltered μ B]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶
      (ihom (join (Δ[0] : SSet.{u + 1})
        ((SSet.uliftFunctor.{u + 1, u}).obj K))).obj SpaceInfinity.{u})
    (c : JoinCocone F), IsPointwiseColimitCone c →
      (∀ b : B _⦋0⦌, IsLimitCone (functorVertexCone (F.app
        (Opposite.op ⦋0⦌) (ULift.up b)))) → IsLimitCone (functorVertexCone c.vertex)

/-- 同型な形状の交換は、元の全余錐を保つ前合成によって輸送される。 -/
lemma CardinalFilteredLimitExchangeShape.of_iso {μ : Cardinal.{u}} {L K : SSet.{u}}
    (e : L ≅ K) (h : CardinalFilteredLimitExchangeShape μ L) :
    CardinalFilteredLimitExchangeShape μ K := by
  intro B hB hμ F c hc hF
  let r := (SSet.uliftFunctor.{u + 1, u}).map e.hom
  let q := (pre (joinMap (𝟙 (Δ[0] : SSet.{u + 1})) r)).app SpaceInfinity.{u}
  have ht := h B (F ≫ q) (mapJoinCocone q c)
    (pointwiseColimitCocone_precomp c hc _)
    (fun b ↦ (isLimitCone_functorVertexCone_reindex_iff r
      (F.app (Opposite.op ⦋0⦌) (ULift.up b))).mpr (hF b))
  rw [Ind.mapJoinCocone_vertex] at ht
  exact (isLimitCone_functorVertexCone_reindex_iff r c.vertex).mp ht

/-- 実証済みの小さい poset の全錐交換を、指定形状の述語として公開する。 -/
lemma cardinalFilteredLimitExchangeShape_poset
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : IsCardinalChangeBound κ μ) (I : Type u) [PartialOrder I] (hI : HasCardinalLT I μ) :
    CardinalFilteredLimitExchangeShape μ (nerve I) :=
  coherentCardinalFilteredLimitExchange_poset h I hI

/-- N の大きい Hom 錐の元の反対形状に対する、同じ持ち上げた濃度での全交換の実証拠。 -/
lemma cardinalFilteredLimitExchangeShape_ulift_poset_op
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : IsCardinalChangeBound κ μ) (I : Type u) [PartialOrder I] (hI : HasCardinalLT I μ) :
    CardinalFilteredLimitExchangeShape (Cardinal.lift.{v} μ)
      (((SSet.uliftFunctor.{v, u}).obj (nerve I)).op) := by
  have : Fact (Cardinal.lift.{v} κ).IsRegular := ⟨(Fact.out : κ.IsRegular).lift⟩
  have : Fact (Cardinal.lift.{v} μ).IsRegular := ⟨(Fact.out : μ.IsRegular).lift⟩
  have hi : HasCardinalLT (ULift.{v} (OrderDual I)) (Cardinal.lift.{v} μ) := by
    have hd : HasCardinalLT (OrderDual I) μ := hI
    simpa only [hasCardinalLT_lift_iff, hasCardinalLT_ulift_iff] using hd
  exact (cardinalFilteredLimitExchangeShape_poset h.lift _ hi).of_iso
    (nervePosetUniverseOppositeIso.{u, v} I).symm

end SerrePositivity.InfinityCategories.F2.Presentable
