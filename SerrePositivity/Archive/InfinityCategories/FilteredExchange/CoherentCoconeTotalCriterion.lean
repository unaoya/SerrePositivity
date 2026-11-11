module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoherentCoconeTotalComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconePointHomInitiality

/-!
概要：一般 coherent 空間値図式の余極限性を、元の全空間を共通模型とする全 Hom で判定する。
方針：証明済みの余錐空間の比較同値を N の全 Hom の判定で消去する。
規約：元の余錐に余極限性を仮定せず、実際の比較族の同値性を残る証明課題とする。
使われ方：構成済みの全空間余錐と実際の Kan 単位との整合性による最終判定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {B : SSet.{u}}

/-- 概要：実際の余錐の余極限性は全 Hom の族と全空間比較の合成の同値性で判定できる。
方針：比較のホモトピー同値性を、N の元の余錐の始対象性の判定と組み合わせる。
規約：候補頂点の同値だけではなく実際の全 Hom の族を検査する。 -/
lemma isColimitCone_iff_coherentCoconeTotalComparison
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (c : JoinCocone F) :
    IsColimitCone c ↔ ∀ z : SpaceInfinity.{u} _⦋0⦌,
      IsSimplicialHomotopyEquivalence
        (coconePointHomFamily c z ≫ coherentCoconeTotalComparison F z) := by
  constructor
  · intro hc z
    exact (coconePointHomFamily_homotopyEquivalence c hc z).comp
      (coherentCoconeTotalComparison_homotopyEquivalence F z)
  · intro h
    exact isColimitCone_of_pointHomFamily_comparison c
      (fun z ↦ (SSet.uliftFunctor.{u + 1, u}).obj
        ((CategoryTheory.ihom (smallLeftUnstraightening F)).obj (spaceInfinityObject z).obj))
      (coherentCoconeTotalComparison F) (coherentCoconeTotalComparison_homotopyEquivalence F) h

end SerrePositivity.InfinityCategories.F2
