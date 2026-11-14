module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGModuleResolvedInvertsQuasiIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGModuleNerveHomotopyEquivalence
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.UniverseVertexIso

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet

open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]

/-- 実分解像が可逆なら元の出力閉射は準同型。 -/
lemma dgModuleResolvedInfinity_reflectsQuasiIso
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
    {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)) x y)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R E)
      (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R C E F)))) :
    moduleQuasiIso R E (F.onClosed.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e)) := by
  let HC := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R C).functor
  let HD := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E)).functor ⋙
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModuleToDerived R E
  let L := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R C E F
  let a := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_classicalIso R C E F ≪≫
    Functor.isoWhiskerLeft HC (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionClassicalComparisonIso R C E F)
  have h₀ : IsIso ((hoFunctor.map L).toFunctor.map
      (Truncated.HomotopyCategory.homMk e)) := he
  let := h₀
  have hL : IsIso (((hoFunctor.map L).toFunctor ⋙ HD).map
      (Truncated.HomotopyCategory.homMk e)) := HD.map_isIso _
  have hi := (NatIso.isIso_map_iff a _).mp hL
  change IsIso ((_root_.SerrePositivity.DifferentialGraded.moduleHomotopyToDerivedClosed R E).map
    (F.onHomotopy.map (HC.map (Truncated.HomotopyCategory.homMk e)))) at hi
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence_map_homMk] at hi
  have ht : IsIso ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R E ⋙ _root_.SerrePositivity.DifferentialGraded.moduleHomotopyToDerivedClosed R E).map
      (F.onClosed.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e))) := hi
  exact (_root_.SerrePositivity.DifferentialGraded.moduleToDerived_map_isIso_iff R E _).mp
    ((NatIso.isIso_map_iff (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopyDerivedIso R E) _).mp ht)

/-- 実分解が写す辺の可逆性と元の出力閉射の準同型性の同値。 -/
lemma dgModuleResolvedInfinity_isInvertibleEdge_iff
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
    {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R E)
      (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R C E F))) ↔
      moduleQuasiIso R E (F.onClosed.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e)) :=
  ⟨dgModuleResolvedInfinity_reflectsQuasiIso R C E F e,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_invertsQuasiIso R C E F e⟩

/-- 任意の追加宇宙へ持ち上げた実分解像でも同じ準同型性を検出する。 -/
lemma dgModuleResolvedInfinity_ulift_isInvertibleEdge_iff
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
    {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (SSet.uliftFunctor.{w}).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R E)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{max (u + 1) v, w}
      (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R C E F)))) ↔
      moduleQuasiIso R E (F.onClosed.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e)) := by
  constructor
  · intro h
    exact (dgModuleResolvedInfinity_isInvertibleEdge_iff R C E F e).mp h.down
  · intro h
    exact ((dgModuleResolvedInfinity_isInvertibleEdge_iff R C E F e).mpr h).ulift

omit [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] in
/-- 元の任意の閉加群射について、全加群実分解の像が可逆となる判定。 -/
lemma dgModuleResolutionInfinity_isInvertibleEdge_iff
    {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R E} (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R E)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge R E f).toTruncated.map
      ((truncation 2).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id _)))) ↔
      moduleQuasiIso R E f := by
  have h := dgModuleResolvedInfinity_isInvertibleEdge_iff R (_root_.SerrePositivity.DifferentialGraded.RightModule R E) E
    (DGFunctor.id _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge R E f).toTruncated
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge_closed] at h
  simpa only [_root_.SerrePositivity.DifferentialGraded.DGFunctor.onClosed, EnrichedFunctor.forget, _root_.SerrePositivity.DifferentialGraded.DGFunctor.id,
    EnrichedFunctor.id, Category.comp_id, ForgetEnrichment.homOf_homTo] using h

omit [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] in
/-- 元の閉加群射に対する判定は任意の追加 ULift 宇宙でも同じ。 -/
lemma dgModuleResolutionInfinity_ulift_isInvertibleEdge_iff
    {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R E} (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (SSet.uliftFunctor.{w}).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R E)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{max (u + 1) v, w}
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge R E f).toTruncated.map ((truncation 2).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id _))))) ↔
      moduleQuasiIso R E f := by
  constructor
  · intro h
    exact (dgModuleResolutionInfinity_isInvertibleEdge_iff R E f).mp h.down
  · intro h
    exact ((dgModuleResolutionInfinity_isInvertibleEdge_iff R E f).mpr h).ulift

end SerrePositivity.InfinityCategories.Project.DerivedCategories
