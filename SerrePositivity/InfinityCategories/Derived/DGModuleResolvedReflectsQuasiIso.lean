module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedInvertsQuasiIso
public import SerrePositivity.InfinityCategories.Derived.DGModuleNerveHomotopyEquivalence
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.InfinityCategories.F1.UniverseVertexIso

/-!
概要：実半自由分解での辺の可逆性は、元の出力閉射の準同型性を検出する。
方針：実分解の通常のホモトピー圏比較を通じ、指定導来局所化の検出定理へ戻す。
規約：Small は係数 dg 圏だけに課し、任意の追加 ULift 宇宙を許す。
使われ方：D2 G-1 f の全加群実分解による準同型の反映と同値判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open DGNerve.HomotopyComparison
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E]

/-- 実分解像が可逆なら元の出力閉射は準同型。 -/
lemma dgModuleResolvedInfinity_reflectsQuasiIso
    (F : DGFunctor R C (RightModule R E))
    {x y : (dgNerve R C) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (dgNerve R C)) x y)
    (he : IsInvertibleEdge (X := dgModuleDerivedInfinityCategory R E)
      (e.map ((truncation 2).map (dgModuleResolvedInfinity R C E F)))) :
    moduleQuasiIso R E (F.onClosed.map (edgeClosed e)) := by
  let HC := (dgStableHomotopyEquivalence R C).functor
  let HD := (dgStableHomotopyEquivalence R (SemifreeDGModules R E)).functor ⋙
    dgSemifreeModuleToDerived R E
  let L := dgModuleResolvedInfinity R C E F
  let a := dgModuleResolvedInfinity_classicalIso R C E F ≪≫
    Functor.isoWhiskerLeft HC (dgModuleOutputResolutionClassicalComparisonIso R C E F)
  have h₀ : IsIso ((hoFunctor.map L).toFunctor.map
      (Truncated.HomotopyCategory.homMk e)) := he
  let := h₀
  have hL : IsIso (((hoFunctor.map L).toFunctor ⋙ HD).map
      (Truncated.HomotopyCategory.homMk e)) := HD.map_isIso _
  have hi := (NatIso.isIso_map_iff a _).mp hL
  change IsIso ((moduleHomotopyToDerivedClosed R E).map
    (F.onHomotopy.map (HC.map (Truncated.HomotopyCategory.homMk e)))) at hi
  rw [dgStableHomotopyEquivalence_map_homMk] at hi
  have ht : IsIso ((moduleToHomotopy R E ⋙ moduleHomotopyToDerivedClosed R E).map
      (F.onClosed.map (edgeClosed e))) := hi
  exact (moduleToDerived_map_isIso_iff R E _).mp
    ((NatIso.isIso_map_iff (moduleToHomotopyDerivedIso R E) _).mp ht)

/-- 実分解が写す辺の可逆性と元の出力閉射の準同型性の同値。 -/
lemma dgModuleResolvedInfinity_isInvertibleEdge_iff
    (F : DGFunctor R C (RightModule R E))
    {x y : (dgNerve R C) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (dgNerve R C)) x y) :
    IsInvertibleEdge (X := dgModuleDerivedInfinityCategory R E)
      (e.map ((truncation 2).map (dgModuleResolvedInfinity R C E F))) ↔
      moduleQuasiIso R E (F.onClosed.map (edgeClosed e)) :=
  ⟨dgModuleResolvedInfinity_reflectsQuasiIso R C E F e,
    dgModuleResolvedInfinity_invertsQuasiIso R C E F e⟩

/-- 任意の追加宇宙へ持ち上げた実分解像でも同じ準同型性を検出する。 -/
lemma dgModuleResolvedInfinity_ulift_isInvertibleEdge_iff
    (F : DGFunctor R C (RightModule R E))
    {x y : (dgNerve R C) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (dgNerve R C)) x y) :
    IsInvertibleEdge (X := (SSet.uliftFunctor.{w}).obj
      (dgModuleDerivedInfinityCategory R E)) (uliftTruncatedEdge.{max (u + 1) v, w}
      (e.map ((truncation 2).map (dgModuleResolvedInfinity R C E F)))) ↔
      moduleQuasiIso R E (F.onClosed.map (edgeClosed e)) := by
  constructor
  · intro h
    exact (dgModuleResolvedInfinity_isInvertibleEdge_iff R C E F e).mp h.down
  · intro h
    exact ((dgModuleResolvedInfinity_isInvertibleEdge_iff R C E F e).mpr h).ulift

omit [DGCategory R C] in
/-- 元の任意の閉加群射について、全加群実分解の像が可逆となる判定。 -/
lemma dgModuleResolutionInfinity_isInvertibleEdge_iff
    {M N : ModuleCategory R E} (f : M ⟶ N) :
    IsInvertibleEdge (X := dgModuleDerivedInfinityCategory R E)
      ((dgModuleEdge R E f).toTruncated.map
      ((truncation 2).map
        (dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id _)))) ↔
      moduleQuasiIso R E f := by
  have h := dgModuleResolvedInfinity_isInvertibleEdge_iff R (RightModule R E) E
    (DGFunctor.id _) (dgModuleEdge R E f).toTruncated
  rw [dgModuleEdge_closed] at h
  simpa only [DGFunctor.onClosed, EnrichedFunctor.forget, DGFunctor.id,
    EnrichedFunctor.id, Category.comp_id, ForgetEnrichment.homOf_homTo] using h

omit [DGCategory R C] in
/-- 元の閉加群射に対する判定は任意の追加 ULift 宇宙でも同じ。 -/
lemma dgModuleResolutionInfinity_ulift_isInvertibleEdge_iff
    {M N : ModuleCategory R E} (f : M ⟶ N) :
    IsInvertibleEdge (X := (SSet.uliftFunctor.{w}).obj
      (dgModuleDerivedInfinityCategory R E)) (uliftTruncatedEdge.{max (u + 1) v, w}
      ((dgModuleEdge R E f).toTruncated.map ((truncation 2).map
        (dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id _))))) ↔
      moduleQuasiIso R E f := by
  constructor
  · intro h
    exact (dgModuleResolutionInfinity_isInvertibleEdge_iff R E f).mp h.down
  · intro h
    exact ((dgModuleResolutionInfinity_isInvertibleEdge_iff R E f).mpr h).ulift

end SerrePositivity.InfinityCategories
