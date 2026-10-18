module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RightFibrationHomComparison
public import SerrePositivity.InfinityCategories.Core.RelativeEquivalencePathAt
public import SerrePositivity.InfinityCategories.F1.PointFunctorEvaluation
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneIntervalEndpoints

/-!
概要：Kan 複体では全ての path が可逆で、可逆 path の部分複体は通常の関手空間と同型。
方針：ホモトピー圏の亜群性で全ての頂点条件を満たし、全部分複体の包含の逆を作る。
規約：可逆 path の既存の定義を変更しない。
使われ方：Kerodon 4.4.2.1、4.5.3.24、7.5.4.6 の Kan fibration の導来ファイバー。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：Kan 複体を標的とする区間関手の全ての頂点は可逆 path を表す。
方針：Kan 複体のホモトピー圏の全ての射の可逆性を使う。
規約：区間関手の始点と終点は固定しない。
使われ方：Kerodon 4.4.2.1、4.5.3.24 の可逆 path の全部分複体の回収。 -/
lemma isEquivalencePathVertex_of_kanComplex {X : SSet.{u}} [KanComplex X]
    (v : ((ihom (Δ[1] : SSet.{u})).obj X).obj (Opposite.op ⦋0⦌)) :
    IsEquivalencePathVertex v :=
  IsGroupoid.all_isIso (C := hoFunctor.obj X)
    (SSet.Truncated.HomotopyCategory.homMk (edgeOfSimplex (intervalFunctorVertexEdge v)))

/-- 概要：Kan 複体の可逆 path の包含は通常の区間関手空間への厳密な同型。
方針：全ての単体の全頂点が可逆 path なので、包含は各次数で全単射である。
規約：元の包含射そのものの同型性。
使われ方：Kerodon 4.5.3.24、7.5.4.6 の通常の path 充填を可逆 path へ移す。 -/
instance equivalencePathι_isIso_of_kanComplex (X : SSet.{u}) [KanComplex X] :
    IsIso (equivalencePathι X) := by
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
使われ方：Kerodon 4.5.3.24、7.5.4.6 の導来ファイバーの span の Kan 性。 -/
instance equivalencePath_kanComplex (X : SSet.{u}) [KanComplex X] :
    KanComplex (equivalencePath X) :=
  kanComplex_of_iso (asIso (equivalencePathι X)).symm

end SerrePositivity.InfinityCategories.HomotopyLimits
