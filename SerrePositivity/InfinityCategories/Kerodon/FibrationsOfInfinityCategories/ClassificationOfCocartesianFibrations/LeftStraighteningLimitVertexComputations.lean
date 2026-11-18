module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningLimitVertex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.OverEquivalenceLimitSpan

/-!
概要：元の分類図式比較による極限頂点比較を、任意の同じ中間極限で計算する。
方針：元のchooseの値を変えず、既存の三因子の比較の合成則で消去する。
規約：HTT 5.1.5.6・Kerodon Tag 028Tの既存構成の、この模型での計算法則。
使われ方：R04の指定した余単位と頂点射の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の分類図式比較の三因子は、任意の同じ中間極限錐を使って計算できる。
HTT 5.1.5.6・Kerodon Tag 028Tの構成に付随する、この指定比較での計算法則。 -/
@[cite HTT "5.1.5.6" (partial := special) "元の分類同型から作る極限頂点比較の中間極限の選択を消去する法則。"]
lemma limitVertexIsoOfLeftStraighteningIso_eq_middle
    {E F B X : SSet.{u}} [Quasicategory E] [Quasicategory F]
    [Quasicategory B] [Quasicategory X]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (e : FunctorIso (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q))
    (O : B ⟶ X) (c : JoinCone (p ≫ O)) (d : JoinCone (q ≫ O))
    (hc : IsLimitCone c) (hd : IsLimitCone d)
    (s : JoinCone (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p) ≫ O))
    (t : JoinCone (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q) ≫ O))
    (hs : IsLimitCone s) (ht : IsLimitCone t) :
    limitVertexIsoOfLeftStraighteningIso p q e O c d hc hd =
      limitVertexIsoOfOverEquivalence (leftStraighteningInfinityReconstruction p)
        (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence p).isQCatEquivalence
        (leftStraighteningInfinityReconstruction_projection p) O c s hc hs ≪≫
      limitVertexIsoOfOverEquivalence (smallLeftUnstraighteningComparisonOfFunctorIso e)
        (smallLeftUnstraighteningComparisonOfFunctorIso_isPrecompositionEquivalence e).isQCatEquivalence
        (smallLeftUnstraighteningComparisonOfFunctorIso_projection e) O s t hs ht ≪≫
      (limitVertexIsoOfOverEquivalence (leftStraighteningInfinityReconstruction q)
        (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence q).isQCatEquivalence
        (leftStraighteningInfinityReconstruction_projection q) O d t hd ht).symm := by
  let hp : HasLimit (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p) ≫ O) := ⟨s, hs⟩
  let hq : HasLimit (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q) ≫ O) := ⟨t, ht⟩
  let s₀ := Classical.choose hp
  let t₀ := Classical.choose hq
  have hs₀ := Classical.choose_spec hp
  have ht₀ := Classical.choose_spec hq
  change limitVertexIsoOfOverEquivalence (leftStraighteningInfinityReconstruction p)
      (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence p).isQCatEquivalence
      (leftStraighteningInfinityReconstruction_projection p) O c s₀ hc hs₀ ≪≫
    limitVertexIsoOfOverEquivalence (smallLeftUnstraighteningComparisonOfFunctorIso e)
      (smallLeftUnstraighteningComparisonOfFunctorIso_isPrecompositionEquivalence e).isQCatEquivalence
      (smallLeftUnstraighteningComparisonOfFunctorIso_projection e) O s₀ t₀ hs₀ ht₀ ≪≫
    (limitVertexIsoOfOverEquivalence (leftStraighteningInfinityReconstruction q)
      (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence q).isQCatEquivalence
      (leftStraighteningInfinityReconstruction_projection q) O d t₀ hd ht₀).symm = _
  exact limitVertexIsoOfOverEquivalence_span_middle
    (leftStraighteningInfinityReconstruction p) (smallLeftUnstraighteningComparisonOfFunctorIso e)
    (leftStraighteningInfinityReconstruction q)
    (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence p).isQCatEquivalence
    (smallLeftUnstraighteningComparisonOfFunctorIso_isPrecompositionEquivalence e).isQCatEquivalence
    (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence q).isQCatEquivalence
    (leftStraighteningInfinityReconstruction_projection p)
    (smallLeftUnstraighteningComparisonOfFunctorIso_projection e)
    (leftStraighteningInfinityReconstruction_projection q) O c d s₀ s t₀ t hc hd hs₀ hs ht₀ ht

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
