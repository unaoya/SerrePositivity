module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedClassicalComparison
public import SerrePositivity.InfinityCategories.Derived.DGStableHomotopyEdges
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open DGNerve.HomotopyComparison
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E]
/-- 元の辺の出力が準同型なら、実半自由出力分解の同じ辺は可逆。 -/
lemma dgModuleResolvedInfinity_invertsQuasiIso
    (F : DGFunctor R C (RightModule R E))
    {x y : (dgNerve R C) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (dgNerve R C)) x y)
    (he : moduleQuasiIso R E (F.onClosed.map (edgeClosed e))) :
    IsInvertibleEdge (X := dgModuleDerivedInfinityCategory R E)
      (e.map ((truncation 2).map (dgModuleResolvedInfinity R C E F))) := by
  let HC := (dgStableHomotopyEquivalence R C).functor
  let HD := (dgStableHomotopyEquivalence R (SemifreeDGModules R E)).functor ⋙
    dgSemifreeModuleToDerived R E
  let L := dgModuleResolvedInfinity R C E F
  let a := dgModuleResolvedInfinity_classicalIso R C E F ≪≫
    Functor.isoWhiskerLeft HC (dgModuleOutputResolutionClassicalComparisonIso R C E F)
  have ht : IsIso ((moduleToHomotopy R E ⋙ moduleHomotopyToDerivedClosed R E).map
      (F.onClosed.map (edgeClosed e))) :=
    (NatIso.isIso_map_iff (moduleToHomotopyDerivedIso R E) _).mpr
      (moduleToDerived_inverts R E _ he)
  have hi : IsIso ((HC ⋙ F.onHomotopy ⋙ moduleHomotopyToDerivedClosed R E).map
      (Truncated.HomotopyCategory.homMk e)) := by
    change IsIso ((moduleHomotopyToDerivedClosed R E).map
      (F.onHomotopy.map (HC.map (Truncated.HomotopyCategory.homMk e))))
    rw [dgStableHomotopyEquivalence_map_homMk]
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
end SerrePositivity.InfinityCategories
