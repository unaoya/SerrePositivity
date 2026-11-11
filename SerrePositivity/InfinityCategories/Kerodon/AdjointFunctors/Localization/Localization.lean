module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：指定された辺を反転する関手の充満部分 ∞ 圏と局所化の普遍性。
方針：内部 Hom の頂点条件で反転関手を取り、前合成の因子化を構成する。
規約：局所化の存在は公理にも定理にも追加しない。宇宙 u 内の標的で述べる。
使われ方：Kerodon Def 6.3.1.9（Tag 01MP）・Prop 6.3.1.13（Tag 01MS）、HTT §5.2.7 の反射的な場合。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

/-- 概要：関手が可逆にする辺の集合。
方針：元の辺を h の射として可逆になるかで判定する。
規約：X,D の quasicategory 性はこの定義には不要。
使われ方：反射が反転する辺と局所化の標的条件。 -/
@[kerodon 04JH]
def invertedEdges {X D : SSet.{u}} (F : X ⟶ D) : Set (X _⦋1⦌) :=
  {s | _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s).map ((truncation 2).map F))}

/-- 概要：指定された全ての辺を関手が反転するという条件。
方針：辺の集合の包含で定義する。
規約：退化辺・合成などに関する W の閉性は要求しない。
使われ方：局所化に沿って因子化する関手の頂点条件。 -/
def InvertsEdges {X D : SSet.{u}} (F : X ⟶ D) (W : Set (X _⦋1⦌)) : Prop :=
  W ⊆ invertedEdges F

/-- 概要：辺を反転する条件は任意の関手の後合成で保たれる。
方針：可逆な h の射は関手で写しても可逆であることを使う。
規約：quasicategory 性は不要。使われ方：前合成の反転関手圏への因子化。 -/
lemma InvertsEdges.comp {X D E : SSet.{u}} {F : X ⟶ D} {W : Set (X _⦋1⦌)}
    (hF : InvertsEdges F W) (H : D ⟶ E) : InvertsEdges (F ≫ H) W := by
  intro s hs
  exact (hF hs).map H

/-- 概要：W の全ての辺を反転する内部 Hom の頂点の条件。
方針：関手単体集合の頂点を元の単体集合の射へ戻して判定する。
規約：頂点の表示の全単射を使う。使われ方：反転関手の充満部分複体。 -/
def IsInvertingFunctorVertex (X E : SSet.{u}) (W : Set (X _⦋1⦌))
    (v : ((ihom X).obj E) _⦋0⦌) : Prop :=
  InvertsEdges ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv X E).symm v) W

/-- 概要：W を反転する関手からなる充満部分単体集合。
方針：内部 Hom の反転頂点条件の全部分複体を取る。
規約：E が quasicategory ならこれも quasicategory。
使われ方：Kerodon Notation 6.3.1.1（Tag 01MF） の Fun(X[W⁻¹],E)。 -/
@[kerodon 01MF]
def invertingFunctors (X E : SSet.{u}) (W : Set (X _⦋1⦌)) : ((ihom X).obj E).Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom X).obj E) (IsInvertingFunctorVertex X E W)

/-- 概要：quasicategory を標的とする反転関手の圏は quasicategory。
方針：内部 Hom の全部分複体の quasicategory 性を使う。
規約：X の quasicategory 性は不要。使われ方：局所化普遍性の同値の型。 -/
@[kerodon 01MF]
instance invertingFunctors_quasicategory (X E : SSet.{u}) [Quasicategory E]
    (W : Set (X _⦋1⦌)) : Quasicategory (invertingFunctors X E W : SSet.{u}) :=
  inferInstanceAs (Quasicategory
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom X).obj E) (IsInvertingFunctorVertex X E W) : SSet.{u}))

/-- 概要：辺を反転する関手に沿う前合成は反転関手の部分圏に因子化する。
方針：各頂点の関手を表示し、反転条件の後合成不変性を使う。
規約：因子化は元の前合成と厳密に両立する。
使われ方：局所化の普遍性を同値として述べる射。 -/
@[kerodon 01MP]
def localizationPrecomposition {X D : SSet.{u}} (F : X ⟶ D) (W : Set (X _⦋1⦌))
    (hF : InvertsEdges F W) (E : SSet.{u}) :
    (ihom D).obj E ⟶ (invertingFunctors X E W : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (IsInvertingFunctorVertex X E W) ((pre F).app E) (by
    intro v
    obtain ⟨H, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv D E).surjective v
    change InvertsEdges ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv X E).symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv X E) (F ≫ H))) W
    rw [Equiv.symm_apply_apply]
    exact hF.comp H)

/-- 概要：反転関手圏への前合成を含めると元の前合成。
方針：全部分複体への持ち上げの包含公式。
規約：厳密な等式。使われ方：局所化の普遍性の射の識別。 -/
lemma localizationPrecomposition_ι {X D : SSet.{u}} (F : X ⟶ D)
    (W : Set (X _⦋1⦌)) (hF : InvertsEdges F W) (E : SSet.{u}) :
    localizationPrecomposition F W hF E ≫ (invertingFunctors X E W).ι = (pre F).app E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 概要：関手が W に関する局所化を表すという普遍性。
方針：W を反転し、各 quasicategory 標的に対する前合成が反転関手の部分圏との同値であること。
規約：標的は同じ宇宙 u。任意の W に対する局所化の存在は主張しない。
使われ方：Kerodon Prop 6.3.1.13(2)（Tag 01MS） の普遍性と反射的な場合の構成。 -/
@[kerodon 01MP]
def IsLocalization {X D : SSet.{u}} (F : X ⟶ D) (W : Set (X _⦋1⦌)) : Prop :=
  ∃ hF : InvertsEdges F W, ∀ (E : SSet.{u}) [Quasicategory E],
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (localizationPrecomposition F W hF E)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
