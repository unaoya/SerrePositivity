module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeRightOppositeCriterion
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeInternalHomLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration

/-!
概要：元の相対右 Kan 関手の全部分圏と相対制限。
方針：標準局所相対極限条件を頂点条件とし、通常の相対内部 Hom の制限を使う。
規約：始域は元の C 上の関手そのものの全部分複体。
使われ方：左側の制限定理を反転同型で移すための元の右側の射。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：関手頂点が表す F の標準相対右 Kan 条件。
方針：頂点を実際の関手へ戻して局所相対極限性を課す。
規約：写像空間の普遍性を定義には含めない。
使われ方：元の相対右 Kan 関手の全部分複体の頂点条件。 -/
def KanRelativeRightKanVertex {K C D E : SSet.{u}} (U : D ⟶ E) (δ : K ⟶ C)
    (x : ((ihom C).obj D) _⦋0⦌) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeRightKanExtendedFrom U δ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C D).symm x)

/-- 概要：標準相対右 Kan 条件を満たす元の関手の全部分圏。
方針：対応する頂点の張る全部分複体を取る。
規約：相対 join の表示でなく元の関手を対象とする。
使われ方：元の右 Kan 関手全体からの制限の始域。 -/
def kanRelativeRightKanDiagrams {K C D E : SSet.{u}} (U : D ⟶ E) (δ : K ⟶ C) :
    ((ihom C).obj D).Subcomplex := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (KanRelativeRightKanVertex U δ)

/-- 概要：元の相対右 Kan 関手を制限図式と U 像の両立する組へ写す。
方針：全部分複体の包含に通常の相対内部 Hom の比較を合成する。
規約：元の関手圏の単体写像として定義する。
使われ方：元の相対右 Kan 制限定理の比較射。 -/
def kanRelativeRightKanRestriction {K C D E : SSet.{u}} (U : D ⟶ E) (δ : K ⟶ C)
    (s : internalHom.PullbackObjObj δ U) : (kanRelativeRightKanDiagrams U δ : SSet.{u}) ⟶ s.pt :=
  (kanRelativeRightKanDiagrams U δ).ι ≫ s.π

/-- 概要：単射上の元の相対右 Kan 制限は isofibration の上で inner fibration。
方針：相対内部 Hom の同値持ち上げから inner 性を得て、全部分複体の包含と合成する。
規約：右の局所極限の存在は仮定しない。
使われ方：右の写像空間比較と局所存在を全境界充填へ合わせる。 -/
lemma kanRelativeRightKanRestriction_innerFibration {K C D E : SSet.{u}}
    (U : D ⟶ E) (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting U) (δ : K ⟶ C) [Mono δ]
    (s : internalHom.PullbackObjObj δ U) :
    InnerFibration (kanRelativeRightKanRestriction U δ s) := by
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting s.π := by
    intro A B i hm hi
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.relativeInternalHom hU δ s i hm hi
  have : InnerFibration s.π := hs.innerFibration
  have : InnerFibration (kanRelativeRightKanDiagrams U δ).ι :=
    inferInstanceAs (InnerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (KanRelativeRightKanVertex U δ)).ι)
  exact ⟨innerFibrations.comp_mem _ _
    (InnerFibration.mem (q := (kanRelativeRightKanDiagrams U δ).ι))
    (InnerFibration.mem (q := s.π))⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
