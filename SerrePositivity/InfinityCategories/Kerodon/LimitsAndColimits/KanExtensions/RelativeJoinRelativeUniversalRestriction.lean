module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinFunctorRelativeInitial
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexMapping

/-!
概要：局所 U 余極限となる相対 join 図式の全部分圏からの相対制限。
方針：通常の相対制限の写像空間の同値を全部分複体へ制限する。
規約：充満忠実性に局所余極限の存在は要求しない。
使われ方：相対 Kan 図式の写像空間の制限定理と可縮な選択。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：関手頂点の表す図式が全 fiber で標準 U 余極限を与える条件。
方針：関手頂点を図式へ戻して fiber の余錐に条件を課す。
規約：関手の像を定義の入力として固定しない。
使われ方：相対普遍図式の全部分圏の頂点条件。 -/
def KanRelativeJoinRelativeColimitVertex {K C D E : SSet.{u}}
    (p : K ⟶ C) (U : D ⟶ E)
    (x : ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C))).obj D) _⦋0⦌) : Prop :=
  ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinFiberCocone p c
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C)) D).symm x))

/-- 概要：全 fiber で標準 U 余極限となる相対 join 図式の全部分単体集合。
方針：局所相対普遍性の頂点条件で全部分複体を作る。
規約：局所余極限の存在は別途要求する。
使われ方：相対制限の始域となる図式の ∞ 圏。 -/
def kanRelativeJoinRelativeColimitDiagrams {K C D E : SSet.{u}}
    (p : K ⟶ C) (U : D ⟶ E) : ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C))).obj D).Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (KanRelativeJoinRelativeColimitVertex p U)

/-- 概要：局所 U 余極限図式を元の図式と標的の全図式の整合する組へ制限する。
方針：全部分複体の包含の後で相対内部 Hom の比較を取る。
規約：相対内部 Hom の pullback の選択は明示する。
使われ方：普遍図式の coherent な選択と写像空間の比較。 -/
def kanRelativeJoinRelativeColimitRestriction {K C D E : SSet.{u}}
    (p : K ⟶ C) (U : D ⟶ E)
    (sr : internalHom.PullbackObjObj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl p (𝟙 C)) U) :
    (kanRelativeJoinRelativeColimitDiagrams p U : SSet.{u}) ⟶ sr.pt :=
  (kanRelativeJoinRelativeColimitDiagrams p U).ι ≫ sr.π

/-- 概要：相対普遍図式の全部分圏からの相対制限は inner fibration。
方針：右持ち上げ条件の相対内部 Hom による保存と全部分複体の充填性を合成する。
規約：U 自体の始域・標的の充填性をこの結論には要求しない。
使われ方：写像空間の充満忠実性と頂点全射性から自明 Kan 性へ進む。 -/
lemma kanRelativeJoinRelativeColimitRestriction_innerFibration {K C D E : SSet.{u}}
    (p : K ⟶ C) (U : D ⟶ E) (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting U)
    (sr : internalHom.PullbackObjObj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl p (𝟙 C)) U) :
    InnerFibration (kanRelativeJoinRelativeColimitRestriction p U sr) := by
  have hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting sr.π := by
    intro A B i hm hi
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.relativeInternalHom hU _ sr i hm hi
  have : InnerFibration sr.π := hl.innerFibration
  have : InnerFibration (kanRelativeJoinRelativeColimitDiagrams p U).ι :=
    inferInstanceAs (InnerFibration
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (KanRelativeJoinRelativeColimitVertex p U)).ι)
  exact ⟨innerFibrations.comp_mem _ _
    (InnerFibration.mem (q := (kanRelativeJoinRelativeColimitDiagrams p U).ι))
    (InnerFibration.mem (q := sr.π))⟩

/-- 概要：局所 U 余極限図式の全部分圏からの相対制限は充満忠実。
方針：始点の局所普遍性による写像空間の同値と全部分圏の包含の同値を合成する。
規約：局所余極限が存在するという仮定を追加しない。
使われ方：相対 Kan 拡張全体の写像空間の普遍性。 -/
lemma kanRelativeJoinRelativeColimitRestriction_isFullyFaithful {K C D E : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (p : K ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (U : D ⟶ E) (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting U)
    (sr : internalHom.PullbackObjObj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl p (𝟙 C)) U) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (kanRelativeJoinRelativeColimitRestriction p U sr) := by
  have : InnerFibration U := hU.innerFibration
  have : Quasicategory sr.pt := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeInternalHomTarget_quasicategory U _ sr
  have : Quasicategory
      ((internalHom.obj (Opposite.op (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C)))).obj D) :=
    inferInstanceAs (Quasicategory ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C))).obj D))
  intro x y
  have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex x
  change KanRelativeJoinRelativeColimitVertex p U x.val at hx
  let H := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C)) D).symm x.val
  have hH : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H = x.val := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ D).apply_symm_apply _
  have hinit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting sr.π x.val := by
    rw [← hH]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinFunctor_relative_initialBoundary p U hU sr H hx
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap
    ((kanRelativeJoinRelativeColimitDiagrams p U).ι ≫ sr.π) x y)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap_comp]
  exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _ x y).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pinchedHomMap_equivalence_of_initialBoundary _ x.val y.val hinit)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
