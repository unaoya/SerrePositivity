module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CofinalFunctorFamilies
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath

/-!
概要：底上の射と相対関手空間の頂点の対応。
方針：通常の関手頂点に底の固定条件を添える。
規約：F1 の同じ一般構成を straightening 非依存の相対関手空間に対して証明する。
使われ方：cofinal な fibration の切断を相対関手空間の同値から取り出す。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：底上の射を相対関手空間の頂点にする。
方針：functorVertex に後合成の固定条件を添える。
規約：可換性の証明の選択には依存しない。
使われ方：Kerodon §7.2.1（Tag 02N0）、復元比較の目標となる相対関手の指定。 -/
def cofinalFunctorVertex {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
    (f : A ⟶ E) (hf : f ≫ p = a) : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorSpace p a) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f, by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ p) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) 0
    rw [hf, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]⟩

/-- 概要：相対関手空間の全ての頂点は厳密な底上の射から得られる。
方針：内部 Hom の頂点を通常の射で表し、固定条件を functorVertex の単射性で戻す。
規約：底上の可換性は厳密な等式。
使われ方：Kerodon §7.2.1（Tag 02N0）、写像空間の本質的全射性から比較射を選ぶ。 -/
lemma exists_cofinalFunctorVertex {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorSpace p a) _⦋0⦌) :
    ∃ (f : A ⟶ E) (hf : f ≫ p = a), cofinalFunctorVertex p a f hf = v := by
  obtain ⟨f, hv⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A E).surjective v.val
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f = v.val at hv
  have hf : f ≫ p = a := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
    change ((ihom A).map p).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a
    rw [hv]
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] using v.property
  refine ⟨f, hf, ?_⟩
  apply Subtype.ext
  exact hv

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
