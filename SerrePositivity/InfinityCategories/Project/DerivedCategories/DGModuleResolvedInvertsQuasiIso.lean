module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedClassicalComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStableHomotopyEdges
/-!
概要：出力が準同型である元の実辺を、同じ半自由出力分解は可逆な辺へ送る。
方針：通常の h と H⁰ の全関手比較、元の指定局所化と忠実充満比較を使う。
規約：元の出力の射影性・入力の Small 性を仮定しない。
使われ方：全 augmentation ホモトピーを導来合成の比較同型へ送る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet

open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 元の辺の出力が準同型なら、実半自由出力分解の同じ辺は可逆。 -/
lemma dgModuleResolvedInfinity_invertsQuasiIso
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
    {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)) x y)
    (he : moduleQuasiIso R E (F.onClosed.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R E)
      (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R C E F))) := by
  let HC := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R C).functor
  let HD := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E)).functor ⋙
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModuleToDerived R E
  let L := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R C E F
  let a := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_classicalIso R C E F ≪≫
    Functor.isoWhiskerLeft HC (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionClassicalComparisonIso R C E F)
  have ht : IsIso ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R E ⋙ _root_.SerrePositivity.DifferentialGraded.moduleHomotopyToDerivedClosed R E).map
      (F.onClosed.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e))) :=
    (NatIso.isIso_map_iff (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopyDerivedIso R E) _).mpr
      (_root_.SerrePositivity.DifferentialGraded.moduleToDerived_inverts R E _ he)
  have hi : IsIso ((HC ⋙ F.onHomotopy ⋙ _root_.SerrePositivity.DifferentialGraded.moduleHomotopyToDerivedClosed R E).map
      (Truncated.HomotopyCategory.homMk e)) := by
    change IsIso ((_root_.SerrePositivity.DifferentialGraded.moduleHomotopyToDerivedClosed R E).map
      (F.onHomotopy.map (HC.map (Truncated.HomotopyCategory.homMk e))))
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence_map_homMk]
    exact ht
  have hL : IsIso (((hoFunctor.map L).toFunctor ⋙ HD).map
      (Truncated.HomotopyCategory.homMk e)) :=
    (NatIso.isIso_map_iff a _).mpr hi
  have : IsIso (HD.map ((hoFunctor.map L).toFunctor.map
      (Truncated.HomotopyCategory.homMk e))) := hL
  have : IsIso ((hoFunctor.map L).toFunctor.map
      (Truncated.HomotopyCategory.homMk e)) := isIso_of_reflects_iso _ HD
  change IsIso (Truncated.HomotopyCategory.homMk (e.map ((truncation 2).map L)))
  exact this
end SerrePositivity.InfinityCategories.Project.DerivedCategories
