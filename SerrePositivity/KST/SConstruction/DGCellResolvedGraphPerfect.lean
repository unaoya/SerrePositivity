module
public import SerrePositivity.KST.SConstruction.DGCellResolvedGraphArrow
public import SerrePositivity.DifferentialGraded.Morita.QuasiEquivalenceGraph
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction

/-!
概要：同じ制限 graph 解像度の各右制限の導来 perfect 性を証明し、残る射影性を分離する。
方針：cell 増大の準同値による Perf 制限と同じ実解像度の準同型を使う。
規約：解像度右制限の射影性を未証明のまま推論しない。
使われ方：D への追加供給を各実右制限の homotopically projective 性だけへ絞る。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (B : Type v) [DGCategory R B] [Small.{u} B]
local notation "P" => DGCategoryCellResolution.Source R B
local notation "α" => DGCategoryCellResolution.augmentation R B

/-- 概要：元制限 graph の同じ右加群は元代表加群の増大に沿う実制限。
方針：同じ graph と両脚制限の対象作用を回収する。
規約：元加群の等号。使われ方：同じ準同値による導来 Perf 制限。 -/
lemma dgCellRestrictedGraph_evaluation (F : DGFunctor R B B) (x : P) :
    (BimoduleCategory.evaluation R (P) (P) x).obj (dgCellRestrictedGraph R B F) =
      (dgModuleRestriction R (P) B (α).op).onClosed.obj
        (ForgetEnrichment.of (Complex R) (representable R (F.obj ((α).obj x)))) := rfl

/-- 概要：同じ制限 graph の各右加群の導来像は perfect。
方針：元代表加群の Perf 性を同じ cell 増大の準同値で制限する。
規約：射影性は別条件。使われ方：同じ実解像度の Perf 性の回収。 -/
lemma dgCellRestrictedGraph_perfect (F : DGFunctor R B B) (x : P) :
    modulePerfect R (P) ((moduleToDerived R (P)).obj
      ((BimoduleCategory.evaluation R (P) (P) x).obj (dgCellRestrictedGraph R B F))) := by
  let M := ForgetEnrichment.of (Complex R) (representable R (F.obj ((α).obj x)))
  have hp := quasiEquivalenceRestriction_perfect R (P) B (α)
    (DGCategoryCellResolution.augmentation_quasiEquivalence R B)
    (modulePerfectOver_representable R B (F.obj ((α).obj x)) (Set.mem_univ _))
  exact (modulePerfect R (P)).prop_of_iso
    (dgDerivedRestrictionComputation R (P) B (α) M ≪≫
      eqToIso (congrArg (fun N => (moduleToDerived R (P)).obj N)
        (dgCellRestrictedGraph_evaluation R B F x).symm)) hp

/-- 概要：同じ解像度増大は各右加群の実準同型。
方針：同じ bimodule 解像度の全二変数の準同型を評価する。
規約：元増大を保持。使われ方：実右制限の導来 Perf 性の輸送。 -/
lemma dgCellResolvedGraph_evaluation_quasiIso (F : DGFunctor R B B) (x : P) :
    moduleQuasiIso R (P) ((BimoduleCategory.evaluation R (P) (P) x).map
      (dgCellResolvedGraphResolution R B F).π) := by
  intro y
  exact (dgCellResolvedGraphResolution R B F).value_quasiIso y x

/-- 概要：同じ解像度 graph の各右加群の導来像は perfect。
方針：同じ実増大の可逆な導来像で元制限 graph の Perf 性を戻す。
規約：射影性は主張しない。使われ方：追加供給の残りを射影性だけにする。 -/
lemma dgCellResolvedGraph_perfect (F : DGFunctor R B B) (x : P) :
    modulePerfect R (P) ((moduleToDerived R (P)).obj
      ((BimoduleCategory.evaluation R (P) (P) x).obj (dgCellResolvedGraphResolution R B F).obj)) := by
  let f := (BimoduleCategory.evaluation R (P) (P) x).map (dgCellResolvedGraphResolution R B F).π
  letI : IsIso ((moduleToDerived R (P)).map f) :=
    moduleToDerived_inverts R (P) f (dgCellResolvedGraph_evaluation_quasiIso R B F x)
  exact (modulePerfect R (P)).prop_of_iso (asIso ((moduleToDerived R (P)).map f)).symm
    (dgCellRestrictedGraph_perfect R B F x)

/-- 概要：同じ実解像度 graph の各右制限が射影的であるという未供給条件。
方針：同じ標準解像度と全 cell 対象を固定する。
規約：存在は未証明。使われ方：D 向けの最小追加供給型。 -/
def DGCellResolvedGraphProjectiveCondition (F : DGFunctor R B B) : Prop :=
  ∀ x : P, moduleHomotopicallyProjective R (P)
    ((BimoduleCategory.evaluation R (P) (P) x).obj (dgCellResolvedGraphResolution R B F).obj)

/-- 概要：同じ実右制限の射影性だけで射影的 perfect 条件を充足する。
方針：証明済み導来 Perf 性と同じ射影性を束ねる。
規約：追加仮定を射影性だけに限定。使われ方：D 供給後の実 Perf 関手の構成。 -/
lemma dgCellResolvedGraphPerfectCondition_of_projective (F : DGFunctor R B B)
    (h : DGCellResolvedGraphProjectiveCondition R B F) : DGCellResolvedGraphPerfectCondition R B F :=
  fun x => ⟨h x, dgCellResolvedGraph_perfect R B F x⟩
end SerrePositivity.KST.SConstruction
