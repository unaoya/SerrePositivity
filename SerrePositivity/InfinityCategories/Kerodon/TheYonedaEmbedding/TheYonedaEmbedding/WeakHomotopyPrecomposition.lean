module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanWeakFunctoriality
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulCalculus

/-!
概要：任意の弱ホモトピー同値による Kan 標的への前合成は単体的ホモトピー同値。
方針：連続 Kan 置換の単位の前合成を消去し、Kan 値の Whitehead 判定を使う。
規約：元の始域・終域に Kan 性は不要。
使われ方：反転 augmentation の弱同値性を実際の Hom 比較の同値性へ移す。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding


/-- 概要：弱同値の Kan 標的への前合成は実際の単体的ホモトピー逆を持つ。
方針：単位の自然性の正方形を前合成で反転し、三つの同値から残りを得る。
規約：弱同値の元の二対象は任意。使われ方：native な普遍性の写像空間判定。 -/
lemma pre_isSimplicialHomotopyEquivalence_of_weakHomotopyEquivalence
    {A B : SSet.{u}} (f : A ⟶ B) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence f)
    (Z : SSet.{u}) [KanComplex Z] : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence ((pre f).app Z) := by
  have hQ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacement_map_isWeakHomotopyEquivalence f hf
  have hqEquiv := hQ.isSimplicialHomotopyEquivalence.isQCatEquivalence
  have hpreQ := hqEquiv.isPrecompositionEquivalence Z
  have hA := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.homotopyEquivalence_pre_of_anodyne _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit_anodyne A) Z
  have hB := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.homotopyEquivalence_pre_of_anodyne _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit_anodyne B) Z
  have hn : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app B =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality f
  have hp := congrArg (fun t ↦ (pre t).app Z) hn
  simp only [pre_map, NatTrans.comp_app] at hp
  apply hB.cancel_left
  rw [hp]
  exact hpreQ.isSimplicialHomotopyEquivalence.comp hA

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
