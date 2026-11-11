module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.RightFibrationHomComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.RelativeEquivalencePathAt
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneIntervalEndpoints

/-!
概要：Kan 複体では全ての path が可逆で、可逆 path の部分複体は通常の関手空間と同型。
方針：ホモトピー圏の亜群性で全ての頂点条件を満たし、全部分複体の包含の逆を作る。
規約：可逆 path の既存の定義を変更しない。
使われ方：Kerodon 4.4.2.1（Tag 019D）、4.5.3.24（Tag 02VM）、7.5.4.6（Tag 03BB） の Kan fibration の導来ファイバー。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：Kan 複体を標的とする区間関手の全ての頂点は可逆 path を表す。
方針：Kan 複体のホモトピー圏の全ての射の可逆性を使う。
規約：区間関手の始点と終点は固定しない。
使われ方：Kerodon 4.4.2.1（Tag 019D）、4.5.3.24（Tag 02VM） の可逆 path の全部分複体の回収。 -/
lemma isEquivalencePathVertex_of_kanComplex {X : SSet.{u}} [KanComplex X]
    (v : ((ihom (Δ[1] : SSet.{u})).obj X).obj (Opposite.op ⦋0⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex v :=
  IsGroupoid.all_isIso (C := hoFunctor.obj X)
    (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge v)))

/-- 概要：Kan 複体の可逆 path の包含は通常の区間関手空間への厳密な同型。
方針：全ての単体の全頂点が可逆 path なので、包含は各次数で全単射である。
規約：元の包含射そのものの同型性。
使われ方：Kerodon 4.5.3.24（Tag 02VM）、7.5.4.6（Tag 03BB） の通常の path 充填を可逆 path へ移す。 -/
instance equivalencePathι_isIso_of_kanComplex (X : SSet.{u}) [KanComplex X] :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro d
  rw [isIso_iff_bijective]
  refine ⟨Subtype.val_injective, ?_⟩
  intro s
  refine ⟨⟨s, ?_⟩, rfl⟩
  intro v
  exact isEquivalencePathVertex_of_kanComplex _

/-- 概要：Kan 複体の可逆 path の空間も Kan 複体。
方針：通常の区間関手空間の Kan 性を包含の逆同型で移す。
規約：始点と終点を同時には固定しない。
使われ方：Kerodon 4.5.3.24（Tag 02VM）、7.5.4.6（Tag 03BB） の導来ファイバーの span の Kan 性。 -/
instance equivalencePath_kanComplex (X : SSet.{u}) [KanComplex X] :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso (asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X)).symm

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
